// Copyright 2016 The Cockroach Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied. See the License for the specific language governing
// permissions and limitations under the License.
//
// Author: Andrei Matei (andreimatei1@gmail.com)

package distsql_test

import (
	"testing"

	"golang.org/x/net/context"

	"github.com/cockroachdb/cockroach/base"
	"github.com/cockroachdb/cockroach/keys"
	"github.com/cockroachdb/cockroach/kv"
	"github.com/cockroachdb/cockroach/roachpb"
	"github.com/cockroachdb/cockroach/sql/distsql"
	"github.com/cockroachdb/cockroach/sql/parser"
	"github.com/cockroachdb/cockroach/sql/sqlbase"
	"github.com/cockroachdb/cockroach/testutils/testcluster"
	"github.com/cockroachdb/cockroach/util/leaktest"
	"github.com/cockroachdb/cockroach/util/log"
	"github.com/pkg/errors"
)

func TestResolveLeaseHolders(t *testing.T) {
	defer leaktest.AfterTest(t)()

	tc := testcluster.StartTestCluster(t, 3,
		base.TestClusterArgs{
			ReplicationMode: base.ReplicationManual,
			ServerArgs: base.TestServerArgs{
				UseDatabase: "t",
			},
		})
	defer tc.Stopper().Stop()

	if _, err := tc.Conns[0].Exec(`CREATE DATABASE t`); err != nil {
		t.Fatal(err)
	}
	if _, err := tc.Conns[0].Exec(`CREATE TABLE test (k INT PRIMARY KEY)`); err != nil {
		t.Fatal(err)
	}
	if _, err := tc.Conns[0].Exec(`INSERT INTO test VALUES (1), (2), (3)`); err != nil {
		t.Fatal(err)
	}

	tableDesc := sqlbase.GetTableDescriptor(tc.Servers[0].DB(), "t", "test")
	// Split every SQL row in its own range.
	rowRanges := make([]*roachpb.RangeDescriptor, 4)
	for i := 0; i < 3; i++ {
		var err error
		var l *roachpb.RangeDescriptor
		l, rowRanges[i], err = splitRangeAtKey(tc, tableDesc, i)
		if err != nil {
			t.Fatal(err)
		}
		if i > 0 {
			rowRanges[i-1] = l
		}
	}
	// Replicate the row ranges everywhere.
	for i := 0; i < 3; i++ {
		var err error
		rowRanges[i], err = tc.AddReplicas(
			rowRanges[i].StartKey.AsRawKey(),
			testcluster.ReplicationTarget{
				NodeID:  tc.Servers[1].GetNode().Descriptor.NodeID,
				StoreID: tc.Servers[1].GetFirstStoreID(),
			},
			testcluster.ReplicationTarget{
				NodeID:  tc.Servers[2].GetNode().Descriptor.NodeID,
				StoreID: tc.Servers[2].GetFirstStoreID(),
			})
		if err != nil {
			t.Fatal(err)
		}
	}

	// Scatter the leases around; node i gets range i.
	for i := 0; i < 3; i++ {
		err := tc.TransferRangeLease(rowRanges[i],
			testcluster.ReplicationTarget{
				NodeID:  tc.Servers[i].GetNode().Descriptor.NodeID,
				StoreID: tc.Servers[i].GetFirstStoreID(),
			})
		if err != nil {
			t.Fatal(err)
		}
	}

	// Create a LeaseHolderResolver.
	lhc := kv.NewLeaseHolderCache(100)
	rdc := kv.NewRangeDescriptorCache(tc.Servers[0].GetDistSender(), 100)
	lr := distsql.NewLeaseHolderResolver(lhc, rdc, tc.Servers[0].Gossip(), tc.Servers[0].GetNode().Descriptor)

	var spans []roachpb.Span
	for i := 0; i < 3; i++ {
		spans = append(
			spans,
			roachpb.Span{Key: rowRanges[i].StartKey.AsRawKey(), EndKey: rowRanges[i].EndKey.AsRawKey()})
	}

	// Resolve the spans. Since our caches is empty,
	replicas, err := lr.ResolveLeaseHolders(context.Background(), spans)
	if err != nil {
		t.Fatal(err)
	}
	log.Infof(context.TODO(), "!!! replicas: %s", replicas)
}

// splitRangeAtKey splits the range for a table with schema
// `CREATE TABLE test (k INT PRIMARY KEY)` at row with value pk (the row will be
// the first on the right of the split).
func splitRangeAtKey(
	tc *testcluster.TestCluster, tableDesc *sqlbase.TableDescriptor, pk int,
) (*roachpb.RangeDescriptor, *roachpb.RangeDescriptor, error) {
	if len(tableDesc.Columns) != 1 {
		return nil, nil, errors.Errorf("expected table with one col, got: %+v", tableDesc)
	}
	if tableDesc.Columns[0].Type.Kind != sqlbase.ColumnType_INT {
		return nil, nil, errors.Errorf("expected table with one INT col, got: %+v", tableDesc)
	}

	if len(tableDesc.Indexes) != 0 {
		return nil, nil, errors.Errorf("expected table with just a PK, got: %+v", tableDesc)
	}
	if len(tableDesc.PrimaryIndex.ColumnIDs) != 1 ||
		tableDesc.PrimaryIndex.ColumnIDs[0] != tableDesc.Columns[0].ID ||
		tableDesc.PrimaryIndex.ColumnDirections[0] != sqlbase.IndexDescriptor_ASC {
		return nil, nil, errors.Errorf("table with unexpected PK: %+v", tableDesc)
	}

	pik, err := primaryIndexKey(tableDesc, parser.NewDInt(parser.DInt(pk)))
	if err != nil {
		return nil, nil, err
	}
	startKey := keys.MakeFamilyKey(pik, uint32(tableDesc.Families[0].ID))
	leftRange, rightRange, err := tc.SplitRange(startKey)
	if err != nil {
		return nil, nil, errors.Wrapf(err, "failed to split at row: %d", pk)
	}
	return leftRange, rightRange, nil
}

func primaryIndexKey(tableDesc *sqlbase.TableDescriptor, val parser.Datum) (roachpb.Key, error) {
	primaryIndexKeyPrefix := sqlbase.MakeIndexKeyPrefix(tableDesc, tableDesc.PrimaryIndex.ID)
	colIDtoRowIndex := map[sqlbase.ColumnID]int{tableDesc.Columns[0].ID: 0}
	primaryIndexKey, _, err := sqlbase.EncodeIndexKey(
		tableDesc, &tableDesc.PrimaryIndex, colIDtoRowIndex, []parser.Datum{val}, primaryIndexKeyPrefix)
	if err != nil {
		return nil, err
	}
	return roachpb.Key(primaryIndexKey), nil
}

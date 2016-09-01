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
// Author: David Taylor (david@cockroachlabs.com)
// Author: Andrei Matei (andrei@cockroachlabs.com)

package testcluster

import (
	"testing"
	"time"

	"golang.org/x/net/context"

	"github.com/cockroachdb/cockroach/base"
	"github.com/cockroachdb/cockroach/keys"
	"github.com/cockroachdb/cockroach/roachpb"
	"github.com/cockroachdb/cockroach/rpc"
	"github.com/cockroachdb/cockroach/server/serverpb"
	"github.com/cockroachdb/cockroach/sql/parser"
	"github.com/cockroachdb/cockroach/sql/sqlbase"
	"github.com/cockroachdb/cockroach/testutils"
	"github.com/cockroachdb/cockroach/testutils/sqlutils"
	"github.com/cockroachdb/cockroach/util"
	"github.com/cockroachdb/cockroach/util/leaktest"
	"github.com/cockroachdb/cockroach/util/log"
	"github.com/pkg/errors"
)

func TestManualReplication(t *testing.T) {
	defer leaktest.AfterTest(t)()

	tc := StartTestCluster(t, 3,
		base.TestClusterArgs{
			ReplicationMode: base.ReplicationManual,
			ServerArgs: base.TestServerArgs{
				UseDatabase: "t",
			},
		})
	defer tc.Stopper().Stop()

	s0 := sqlutils.MakeSQLRunner(t, tc.Conns[0])
	s1 := sqlutils.MakeSQLRunner(t, tc.Conns[1])
	s2 := sqlutils.MakeSQLRunner(t, tc.Conns[2])

	s0.Exec(`CREATE DATABASE t`)
	s0.Exec(`CREATE TABLE test (k INT PRIMARY KEY, v INT)`)
	s0.Exec(`INSERT INTO test VALUES (5, 1), (4, 2), (1, 2)`)

	if r := s1.Query(`SELECT * FROM test WHERE k = 5`); !r.Next() {
		t.Fatal("no rows")
	}

	s2.ExecRowsAffected(3, `DELETE FROM test`)

	// Split the table to a new range.
	kvDB := tc.Servers[0].DB()
	tableDesc := sqlbase.GetTableDescriptor(kvDB, "t", "test")

	tableStartKey := keys.MakeRowSentinelKey(keys.MakeTablePrefix(uint32(tableDesc.ID)))
	leftRangeDesc, tableRangeDesc, err := tc.SplitRange(tableStartKey)
	if err != nil {
		t.Fatal(err)
	}
	log.Infof(context.Background(), "After split got ranges: %+v and %+v.", leftRangeDesc, tableRangeDesc)
	if len(tableRangeDesc.Replicas) == 0 {
		t.Fatalf(
			"expected replica on node 1, got no replicas: %+v", tableRangeDesc.Replicas)
	}
	if tableRangeDesc.Replicas[0].NodeID != 1 {
		t.Fatalf(
			"expected replica on node 1, got replicas: %+v", tableRangeDesc.Replicas)
	}

	// Replicate the table's range to all the nodes.
	tableRangeDesc, err = tc.AddReplicas(
		tableRangeDesc.StartKey.AsRawKey(), tc.Target(1), tc.Target(2),
	)
	if err != nil {
		t.Fatal(err)
	}
	if len(tableRangeDesc.Replicas) != 3 {
		t.Fatalf("expected 3 replicas, got %+v", tableRangeDesc.Replicas)
	}
	for i := 0; i < 3; i++ {
		if _, ok := tableRangeDesc.GetReplicaDescriptor(
			tc.Servers[i].GetFirstStoreID()); !ok {
			t.Fatalf("expected replica on store %d, got %+v",
				tc.Servers[i].GetFirstStoreID(), tableRangeDesc.Replicas)
		}
	}

	// Transfer the lease to node 1.
	leaseHolder, err := tc.FindRangeLeaseHolder(
		tableRangeDesc,
		&ReplicationTarget{
			NodeID:  tc.Servers[0].GetNode().Descriptor.NodeID,
			StoreID: tc.Servers[0].GetFirstStoreID(),
		})
	if err != nil {
		t.Fatal(err)
	}
	if leaseHolder.StoreID != tc.Servers[0].GetFirstStoreID() {
		t.Fatalf("expected initial lease on server idx 0, but is on node: %+v",
			leaseHolder)
	}

	err = tc.TransferRangeLease(tableRangeDesc, tc.Target(1))
	if err != nil {
		t.Fatal(err)
	}

	// Check that the lease holder has changed. We'll use the old lease holder as
	// the hint, since it's guaranteed that the old lease holder has applied the
	// new lease.
	leaseHolder, err = tc.FindRangeLeaseHolder(
		tableRangeDesc,
		&ReplicationTarget{
			NodeID:  tc.Servers[0].GetNode().Descriptor.NodeID,
			StoreID: tc.Servers[0].GetFirstStoreID(),
		})
	if err != nil {
		t.Fatal(err)
	}
	if leaseHolder.StoreID != tc.Servers[1].GetFirstStoreID() {
		t.Fatalf("expected lease on server idx 1 (node: %d store: %d), but is on node: %+v",
			tc.Servers[1].GetNode().Descriptor.NodeID,
			tc.Servers[1].GetFirstStoreID(),
			leaseHolder)
	}
}

// A basic test of manual replication that used to fail because we weren't
// waiting for all of the stores to initialize.
func TestBasicManualReplication(t *testing.T) {
	defer leaktest.AfterTest(t)()

	tc := StartTestCluster(t, 3, base.TestClusterArgs{ReplicationMode: base.ReplicationManual})
	defer tc.Stopper().Stop()

	desc, err := tc.AddReplicas(keys.MinKey, tc.Target(1), tc.Target(2))
	if err != nil {
		t.Fatal(err)
	}
	if expected := 3; expected != len(desc.Replicas) {
		t.Fatalf("expected %d replicas, got %+v", expected, desc.Replicas)
	}

	if err := tc.TransferRangeLease(desc, tc.Target(1)); err != nil {
		t.Fatal(err)
	}

	// TODO(peter): Removing the range leader (tc.Target(1)) causes the test to
	// take ~13s vs ~1.5s for removing a non-leader. Track down that slowness.
	desc, err = tc.RemoveReplicas(desc.StartKey.AsRawKey(), tc.Target(0))
	if err != nil {
		t.Fatal(err)
	}
	if expected := 2; expected != len(desc.Replicas) {
		t.Fatalf("expected %d replicas, got %+v", expected, desc.Replicas)
	}
}

func TestWaitForFullReplication(t *testing.T) {
	defer leaktest.AfterTest(t)()

	tc := StartTestCluster(t, 3, base.TestClusterArgs{ReplicationMode: base.ReplicationAuto})
	defer tc.Stopper().Stop()
	if err := tc.WaitForFullReplication(); err != nil {
		t.Error(err)
	}
}

func TestStopServer(t *testing.T) {
	defer leaktest.AfterTest(t)()

	tc := StartTestCluster(t, 3, base.TestClusterArgs{ReplicationMode: base.ReplicationAuto})
	defer tc.Stopper().Stop()
	if err := tc.WaitForFullReplication(); err != nil {
		t.Fatal(err)
	}

	// Connect to server 1, ensure it is answering requests over HTTP and GRPC.
	server1 := tc.Server(1)
	var response serverpb.HealthResponse

	httpClient1, err := server1.GetHTTPClient()
	if err != nil {
		t.Fatal(err)
	}
	url := server1.AdminURL() + "/_admin/v1/health"
	if err := util.GetJSON(httpClient1, url, &response); err != nil {
		t.Fatal(err)
	}

	rpcContext := rpc.NewContext(
		tc.Server(1).RPCContext().Context, tc.Server(1).Clock(), tc.Stopper(),
	)
	conn, err := rpcContext.GRPCDial(server1.ServingAddr())
	if err != nil {
		t.Fatal(err)
	}
	adminClient1 := serverpb.NewAdminClient(conn)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	if _, err := adminClient1.Health(ctx, &serverpb.HealthRequest{}); err != nil {
		t.Fatal(err)
	}

	// Stop server 1.
	tc.StopServer(1)

	// Verify HTTP and GRPC requests to server now fail.
	httpErrorText := "connection refused"
	if err := util.GetJSON(httpClient1, url, &response); err == nil {
		t.Fatal("Expected HTTP Request to fail after server stopped")
	} else if !testutils.IsError(err, httpErrorText) {
		t.Fatalf("Expected error from server with text %q, got error with text %q", httpErrorText, err.Error())
	}

	grpcErrorText := "rpc error"
	if _, err := adminClient1.Health(ctx, &serverpb.HealthRequest{}); err == nil {
		t.Fatal("Expected GRPC Request to fail after server stopped")
	} else if !testutils.IsError(err, grpcErrorText) {
		t.Fatalf("Expected error from GRPC with text %q, got error with text %q", grpcErrorText, err.Error())
	}

	// Verify that request to Server 0 still works.
	httpClient1, err = tc.Server(0).GetHTTPClient()
	if err != nil {
		t.Fatal(err)
	}
	url = tc.Server(0).AdminURL() + "/_admin/v1/health"
	if err := util.GetJSON(httpClient1, url, &response); err != nil {
		t.Fatal(err)
	}
}

// !!! copied from leaseholder_resolver_test
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

// splitRangeAtKey splits the range for a table with schema
// `CREATE TABLE test (k INT PRIMARY KEY)` at row with value pk (the row will be
// the first on the right of the split).
func splitRangeAtKey(
	tc *TestCluster, tableDesc *sqlbase.TableDescriptor, pk int,
) (*roachpb.RangeDescriptor, *roachpb.RangeDescriptor, error) {
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

// !!!
func TestDSQL(t *testing.T) {
	defer leaktest.AfterTest(t)()

	tc := StartTestCluster(t, 3,
		base.TestClusterArgs{
			ReplicationMode: base.ReplicationManual,
			ServerArgs: base.TestServerArgs{
				UseDatabase: "t",
			},
		})
	defer tc.Stopper().Stop()

	s0 := sqlutils.MakeSQLRunner(t, tc.Conns[0])
	s1 := sqlutils.MakeSQLRunner(t, tc.Conns[1])
	s2 := sqlutils.MakeSQLRunner(t, tc.Conns[2])

	s0.Exec(`CREATE DATABASE t`)
	s0.Exec(`CREATE TABLE test (k INT PRIMARY KEY, v INT)`)
	s0.Exec(`INSERT INTO test VALUES (1, 1), (2, 2), (3, 3)`)

	tableDesc := sqlbase.GetTableDescriptor(tc.Servers[0].DB(), "t", "test")
	log.Infof(context.TODO(), "!!! test about to split")
	// Split every SQL row to its own range.
	// TODO(andrei): use the new SQL SPLIT statement when available, and then we
	// also don't need to actually INSERT any data any more.
	rowRanges := make([]*roachpb.RangeDescriptor, 4)
	for i := 0; i < 3; i++ {
		//s0.Exec(`ALTER TABLE test SPLIT AT ($1)`, i)
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
	log.Infof(context.TODO(), "!!! test done splitting")

	// Replicate the row ranges on all nodes.
	for i := 0; i < 3; i++ {
		var err error
		rowRanges[i], err = tc.AddReplicas(
			rowRanges[i].StartKey.AsRawKey(), tc.Target(1), tc.Target(2))
		if err != nil {
			t.Fatal(err)
		}
	}
	log.Infof(context.TODO(), "!!! test done replicating")

	// Scatter the leases around; node i gets range i.
	for i := 0; i < 3; i++ {
		if err := tc.TransferRangeLease(rowRanges[i], tc.Target(i)); err != nil {
			t.Fatal(err)
		}
			rowRanges[i], i)
		// Wait for everybody to apply the new lease, so that we can rely on the
		// lease discovery done later by the LeaseHolderResolver to be up to date.
		util.SucceedsSoon(t, func() error {
			for j := 0; j < 3; j++ {
				target := tc.Target(j)
				rt, err := tc.FindRangeLeaseHolder(rowRanges[i], &target)
				if err != nil {
					t.Fatal(err)
				}
				if rt != tc.Target(i) {
					return errors.Errorf("node %d hasn't applied the lease yet", j)
				}
			}
			return nil
		})
	}
	log.Infof(context.TODO(), "!!! test done moving leases")

	if r := s1.Query(`SELECT * FROM test WHERE v = 3`); !r.Next() {
		t.Fatal("no rows")
	} else {
		r.Close()
	}

	// Evict the descriptor for range 1 from the cache. It's probably stale since
	// this test has been mocking with that range. And a stale descriptor would
	// affect our resolving.
	rdc := tc.Servers[2].DistSender().GetRangeDescriptorCache()
	err := rdc.EvictCachedRangeDescriptor(roachpb.RKeyMin, nil, false /* inclusive */)
	if err != nil {
		t.Fatal(err)
	}

	// !!!
	s2.DB.SetMaxOpenConns(1)
	s2.Exec(`SET DIST_SQL=true`)

	log.Infof(context.TODO(), "!!! distsql: test 1st try")
	if r := s2.Query(`SELECT * FROM test WHERE v = 3`); !r.Next() {
		t.Fatal("no rows")
	} else {
		r.Close()
	}

	time.Sleep(time.Second)
	log.Infof(context.TODO(), "!!! distsql: test 2nd try")

	rows := s2.Query(`SELECT * FROM test WHERE v = 3`)
	gotRows := false
	for rows.Next() {
		gotRows = true
		var k, v int
		err = rows.Scan(&k, &v)
		if err != nil {
			t.Fatal(err)
		}
		log.Infof(context.TODO(), "!!! test got row: %d - %d", k, v)
	}
	if !gotRows {
		t.Fatalf("no rows")
	}
	err = rows.Err() // get any error encountered during iteration
	if err != nil {
		t.Fatal(err)
	}
	rows.Close()
}

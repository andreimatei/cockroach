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

package distsqlrun

import (
	"fmt"
	"sync"

	"github.com/pkg/errors"
	"golang.org/x/net/context"

	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/sql/sqlbase"
	"github.com/cockroachdb/cockroach/pkg/util"
	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/cockroachdb/cockroach/pkg/util/tracing"
)

// tableReader is the start of a computation flow; it performs KV operations to
// retrieve rows for a table, runs a filter expression, and passes rows with the
// desired column values to an output RowReceiver.
// See docs/RFCS/distributed_sql.md
type tableReader struct {
	processorBase

	flowCtx *FlowCtx

	tableID   sqlbase.ID
	spans     roachpb.Spans
	limitHint int64

	fetcher sqlbase.MultiRowFetcher
	alloc   sqlbase.DatumAlloc
}

var _ Processor = &tableReader{}

// newTableReader creates a tableReader.
func newTableReader(
	flowCtx *FlowCtx, spec *TableReaderSpec, post *PostProcessSpec, output RowReceiver,
) (*tableReader, error) {
	if flowCtx.nodeID == 0 {
		return nil, errors.Errorf("attempting to create a tableReader with uninitialized NodeID")
	}
	tr := &tableReader{
		flowCtx: flowCtx,
		tableID: spec.Table.ID,
	}

	// We ignore any limits that are higher than this value to avoid any
	// overflows.
	const overflowProtection = 1000000000
	if post.Limit != 0 && post.Limit <= overflowProtection {
		// In this case the ProcOutputHelper will tell us to stop once we emit
		// enough rows.
		tr.limitHint = int64(post.Limit)
	} else if spec.LimitHint != 0 && spec.LimitHint <= overflowProtection {
		// If it turns out that limiHint rows are sufficient for our consumer, we
		// want to avoid asking for another batch. Currently, the only way for us to
		// "stop" is if we block on sending rows and the consumer sets
		// ConsumerDone() on the RowChannel while we block. So we want to block
		// *after* sending all the rows in the limit hint; to do this, we request
		// rowChannelBufSize + 1 more rows:
		//  - rowChannelBufSize rows guarantee that we will fill the row channel
		//    even after limitHint rows are consumed
		//  - the extra row gives us chance to call Push again after we unblock,
		//    which will notice that ConsumerDone() was called.
		//
		// This flimsy mechanism is only useful in the (optimistic) case that the
		// processor that only needs this many rows is our direct, local consumer.
		// If we have a chain of processors and RowChannels, or remote streams, this
		// reasoning goes out the door.
		//
		// TODO(radu, andrei): work on a real mechanism for limits.
		tr.limitHint = spec.LimitHint + rowChannelBufSize + 1
	}

	if post.Filter.Expr != "" {
		// We have a filter so we will likely need to read more rows.
		tr.limitHint *= 2
	}

	types := make([]sqlbase.ColumnType, len(spec.Table.Columns))
	for i := range types {
		types[i] = spec.Table.Columns[i].Type
	}
	if err := tr.init(post, types, flowCtx, output); err != nil {
		return nil, err
	}

	desc := spec.Table
	if _, _, err := initRowFetcher(
		&tr.fetcher, &desc, int(spec.IndexIdx), spec.Reverse, tr.out.neededColumns(), &tr.alloc, spec.Hack,
	); err != nil {
		return nil, err
	}

	tr.spans = make(roachpb.Spans, len(spec.Spans))
	for i, s := range spec.Spans {
		tr.spans[i] = s.Span
	}

	return tr, nil
}

func initRowFetcher(
	fetcher *sqlbase.MultiRowFetcher,
	desc *sqlbase.TableDescriptor,
	indexIdx int,
	reverseScan bool,
	valNeededForCol util.FastIntSet,
	alloc *sqlbase.DatumAlloc,
	hack bool,
) (index *sqlbase.IndexDescriptor, isSecondaryIndex bool, err error) {
	index, isSecondaryIndex, err = desc.FindIndexByIndexIdx(indexIdx)
	if err != nil {
		return nil, false, err
	}

	colIdxMap := make(map[sqlbase.ColumnID]int, len(desc.Columns))
	for i, c := range desc.Columns {
		colIdxMap[c.ID] = i
	}

	tableArgs := sqlbase.MultiRowFetcherTableArgs{
		Desc:             desc,
		Index:            index,
		ColIdxMap:        colIdxMap,
		IsSecondaryIndex: isSecondaryIndex,
		Cols:             desc.Columns,
		ValNeededForCol:  valNeededForCol,
	}
	if err := fetcher.Init(
		reverseScan, true /* returnRangeInfo */, alloc, tableArgs,
	); err != nil {
		return nil, false, err
	}
	if hack {
		fetcher.SetHack(true, makeHackProgram())
	}

	return index, isSecondaryIndex, nil
}

func makeHackProgram() string {
	return `
extern byte my_strcmp(byte_ptr s1, byte l1, byte_ptr s2, byte l2);
extern byte streq(byte_ptr s1, byte l1, byte_ptr s2, byte l2);
extern byte_ptr skip_checksum(byte_ptr s);
extern byte_ptr skip_int(byte_ptr s);
extern byte_ptr skip_byte(byte_ptr s);
extern byte_ptr skip_bytes(byte_ptr s, byte num);

def byte prog_main(byte_ptr k, byte_ptr v) {
  v = skip_checksum(v);
  v = skip_byte(v);  # tuple tag 
  v = skip_byte(v);  # int col tag 
  v = skip_int(v);   # l_orderkey int
  v = skip_byte(v);  # int col tag 
  v = skip_int(v);   # l_partkey int
  v = skip_byte(v);  # int col tag 
  v = skip_int(v);   # l_suppkey int
  v = skip_byte(v);  # int col tag 
  v = skip_int(v);   # l_linenumber int
  v = skip_byte(v);  # decimal col tag 
  var exp_quantity byte_ptr = "\x04348A06A4"
  var exp_extended_price byte_ptr = "\x1505348D204CD7";
  # compare with literal 
  if (streq(exp_quantity, 5, v, 5)) then {
    v = skip_bytes(v, 5);
    if (streq(exp_extended_price, 7, v, 7)) then {
      return 1;
    } else {
      return 0;
    }
  } else {
    return 0;
  }
  return 0;
}
	`
}

// sendMisplannedRangesMetadata sends information about the non-local ranges
// that were read by this tableReader. This should be called after the fetcher
// was used to read everything this tableReader was supposed to read.
func (tr *tableReader) sendMisplannedRangesMetadata(ctx context.Context) {
	rangeInfos := tr.fetcher.GetRangeInfo()
	var misplannedRanges []roachpb.RangeInfo
	for _, ri := range rangeInfos {
		if ri.Lease.Replica.NodeID != tr.flowCtx.nodeID {
			misplannedRanges = append(misplannedRanges, ri)
		}
	}
	if len(misplannedRanges) != 0 {
		var msg string
		if len(misplannedRanges) < 3 {
			msg = fmt.Sprintf("%+v", misplannedRanges[0].Desc)
		} else {
			msg = fmt.Sprintf("%+v...", misplannedRanges[:3])
		}
		log.VEventf(ctx, 2, "tableReader pushing metadata about misplanned ranges: %s",
			msg)
		tr.out.output.Push(nil /* row */, ProducerMetadata{Ranges: misplannedRanges})
	}
}

// Run is part of the processor interface.
func (tr *tableReader) Run(ctx context.Context, wg *sync.WaitGroup) {
	if wg != nil {
		defer wg.Done()
	}

	ctx = log.WithLogTagInt(ctx, "TableReader", int(tr.tableID))
	ctx, span := processorSpan(ctx, "table reader")
	defer tracing.FinishSpan(span)

	txn := tr.flowCtx.txn
	if txn == nil {
		log.Fatalf(ctx, "joinReader outside of txn")
	}

	log.VEventf(ctx, 1, "starting")
	if log.V(1) {
		defer log.Infof(ctx, "exiting")
	}

	// TODO(radu,andrei,knz): set the traceKV flag when requested by the session.
	if err := tr.fetcher.StartScan(
		ctx, txn, tr.spans, true /* limit batches */, tr.limitHint, false, /* traceKV */
	); err != nil {
		log.Errorf(ctx, "scan error: %s", err)
		tr.out.output.Push(nil /* row */, ProducerMetadata{Err: err})
		tr.out.Close()
		return
	}

	for {
		row, _, _, err := tr.fetcher.NextRow(ctx)
		if err != nil || row == nil {
			if err != nil {
				tr.out.output.Push(nil /* row */, ProducerMetadata{Err: err})
			}
			break
		}
		// Emit the row; stop if no more rows are needed.
		consumerStatus, err := tr.out.EmitRow(ctx, row)
		if err != nil || consumerStatus != NeedMoreRows {
			if err != nil {
				tr.out.output.Push(nil /* row */, ProducerMetadata{Err: err})
			}
			break
		}
	}
	tr.sendMisplannedRangesMetadata(ctx)
	sendTraceData(ctx, tr.out.output)
	tr.out.Close()
}

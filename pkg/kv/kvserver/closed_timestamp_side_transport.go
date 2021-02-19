package kvserver

import (
	"context"
	"unsafe"

	"github.com/cockroachdb/cockroach/pkg/kv/kvserver/closedts/ctpb"
	"github.com/cockroachdb/cockroach/pkg/kv/kvserver/kvserverpb"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
)

type sideTransport struct {
	groups [2]ctpb.Group
}

func (t *sideTransport) run(ctx context.Context, s *Store) {
	s.mu.replicas.Range(func(key int64, value unsafe.Pointer) bool {
		rid := roachpb.RangeID(key)
		r := (*Replica)(value)

		r.mu.RLock()
		if !r.mu.quiescent {
			// If we were tracking the range, untrack it. The range is now unquiesced,
			// so closed timestamps will advance through Raft proposals until it
			// quiesces again.
			t.maybeUntrack(rid)
			r.mu.RUnlock()
			return true
		}

		// If we don't have a valid lease, untrack (if it was tracked).
		ls := r.leaseStatusAtRLocked(ctx, s.Clock().NowAsClockTimestamp())
		if ls.State != kvserverpb.LeaseState_VALID || !ls.OwnedBy(s.StoreID()) {
			t.maybeUntrack(rid)
			r.mu.RUnlock()
			return true
		}
		r.mu.RUnlock()

		r.mu.proposalBuf.forwardClosedTimestampLocked()

		return true
	})
}

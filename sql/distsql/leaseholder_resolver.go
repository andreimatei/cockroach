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

package distsql

import (
	"math"

	"github.com/cockroachdb/cockroach/gossip"
	"github.com/cockroachdb/cockroach/keys"
	"github.com/cockroachdb/cockroach/kv"
	"github.com/cockroachdb/cockroach/roachpb"
	"github.com/cockroachdb/cockroach/sql/sqlbase"
	"github.com/cockroachdb/cockroach/util/log"
	"github.com/cockroachdb/cockroach/util/retry"
	"golang.org/x/net/context"
)

// When guessing lease holders, we try to guess the same node for all the ranges
// applicable, until we hit this limit. The rationale is that maybe a bunch of
// those ranges don't have an active lease, so our guess is going to be
// self-fulfilling. If so, we want to collocate the lease holders. But above
// some limit, we prefer to take the parallelism and distribute to multiple
// nodes. The actual number is based on nothing.
const maxPreferredRangesPerLeaseHolder = 10

// LeaseHolderResolver resolves key spans to the lease holder of their
// respective ranges.  Used when planning physical execution of distributed SQL
// queries.
//
// The LeaseHolderResolver also populates the RangeDescriptorCache with missing
// entries. TODO(andrei): figure out a story for updating existing entries in
// the RangeDescriptorCache. As of July 2016, this class has no role in that;
// only the DistSender does it.
//
// The LeaseHolderResolver shares the LeaseHolderCache and the RangeDescriptorCache with the
// DistSender. TODO(andrei): investigate refactoring the DistSender to use this
// same variant of this API for splitting up KV batches.
//
// All public methods are thread-safe.
type LeaseHolderResolver struct {
	leaseHolderCache *kv.LeaseHolderCache
	rangeCache       *kv.RangeDescriptorCache
	gossip           *gossip.Gossip

	// nodeDesc is the descriptor of the current node. It will be used to give
	// preference to the current node when trying to bias leases transfers.
	// TODO(andrei): can the descriptor change at runtime?
	nodeDesc roachpb.NodeDescriptor
}

// NewLeaseHolderResolver creates a new LeaseHolderResolver.
func NewLeaseHolderResolver(
	leaseHolderCache *kv.LeaseHolderCache,
	rangeCache *kv.RangeDescriptorCache,
	gossip *gossip.Gossip,
	nodeDesc roachpb.NodeDescriptor,
) *LeaseHolderResolver {
	return &LeaseHolderResolver{
		leaseHolderCache: leaseHolderCache,
		rangeCache:       rangeCache,
		gossip:           gossip,
		nodeDesc:         nodeDesc,
	}
}

// ResolveLeaseHolders takes a list of spans and returns a list of lease
// holders, one for every range that overlaps the spans.
// The spans need to be disjoint; they also need to be sorted so that the
// prefetching in the range descriptor cache helps us.
// !!! maybe I need to accept reverse spans for some reason? Look again at what
// the deal with "inclusive" is - some functions in DistSender take inclusive as
// an arg. Why?
func (lr *LeaseHolderResolver) ResolveLeaseHolders(
	ctx context.Context, spans []roachpb.Span,
) ([]kv.ReplicaInfo, error) {
	var leaseHolders []kv.ReplicaInfo
	descs, err := lr.getRangeDescriptors(ctx, spans)
	if log.V(3) {
		log.Infof(ctx, "resolved spans %+v to range descriptors: %+v", spans, descs)
	}
	if err != nil {
		return nil, err
	}

	// Keep track of how many ranges we assigned to each node so we can coallesce
	// guesses.
	rangesPerLeaseHolder := make(map[roachpb.NodeID]uint32)
	for _, rangeDesc := range descs {
		var leaseReplicaInfo kv.ReplicaInfo
		leaseReplicaDesc, ok := lr.leaseHolderCache.Lookup(rangeDesc.RangeID)
		if ok {
			// Lease-holder cache hit.
			leaseReplicaInfo.ReplicaDescriptor = leaseReplicaDesc
			nd, err := lr.gossip.GetNodeDescriptor(leaseReplicaDesc.NodeID)
			if err != nil {
				return nil, sqlbase.NewRangeUnavailableError(
					rangeDesc.RangeID, leaseReplicaDesc.NodeID)
			}
			leaseReplicaInfo.NodeDesc = nd
		} else {
			// Lease-holder cache miss. We'll guess a lease holder and start a real
			// lookup in the background.
			leaseHolder, replicas, err := lr.guessLeaseHolder(rangeDesc, rangesPerLeaseHolder)
			if err != nil {
				return nil, err
			}
			leaseReplicaInfo = leaseHolder
			// Populate the cache with the correct lease holder. As a byproduct, also
			// try to elect the replica guessed above to really become a lease holder.
			// Doing this here, early, benefits the command that we'll surely be
			// sending to this presumed lease holder later.
			go lr.writeLeaseHolderToCache(rangeDesc, replicas)
		}
		leaseHolders = append(leaseHolders, leaseReplicaInfo)
		rangesPerLeaseHolder[leaseReplicaInfo.NodeID]++
	}
	return leaseHolders, nil
}

// guessLeaseHolder "guesses" a lease holder for a given range. It gives
// preference to replicas that are "close" to the current node. It also tries to
// coalesce guesses together, so it gives preference to replicas on nodes that
// are already assumed to be lease holders for some other ranges that are going
// to be part of a single query. Finally, it tries not to overload a single
// node.
//
// rangesPerLeaseHolder contains info about what nodes have been already been
// assumed to be lease holders as part of the current query. It is not updated;
// the caller should record the new guess.
//
// It returns the lease holder, and a list of all the replicas of the range. The
// guessed replica is placed at the front of this list.
func (lr *LeaseHolderResolver) guessLeaseHolder(
	desc *roachpb.RangeDescriptor, rangesPerLeaseHolder map[roachpb.NodeID]uint32,
) (kv.ReplicaInfo, kv.ReplicaSlice, error) {
	replicas := kv.NewReplicaSlice(lr.gossip, desc)
	if len(replicas) == 0 {
		// We couldn't get node descriptors for any replicas.
		var nodeIDs []roachpb.NodeID
		for _, r := range desc.Replicas {
			nodeIDs = append(nodeIDs, r.NodeID)
		}
		return kv.ReplicaInfo{}, nil, sqlbase.NewRangeUnavailableError(
			desc.RangeID, nodeIDs...)

	}
	replicas.OptimizeReplicaOrder(&lr.nodeDesc)

	// Look for a guy we've previously guessed as lease holder that's not yet
	// full.
	for i, replicaInfo := range replicas {
		prevAssignedRanges := rangesPerLeaseHolder[replicaInfo.NodeID]
		if prevAssignedRanges != 0 && prevAssignedRanges < maxPreferredRangesPerLeaseHolder {
			replicas.Swap(0, i)
			return replicaInfo, replicas, nil
		}
	}

	// Either no replica was assigned any previous ranges, or all replicas are
	// full. Go through replicas ordered by preference, and pick the least full
	// one.
	var bestLeaseHolderIdx int
	minLoad := uint32(math.MaxUint32)
	for i, replicaDesc := range replicas {
		prevAssignedRanges := rangesPerLeaseHolder[replicaDesc.NodeID]
		if prevAssignedRanges < minLoad {
			bestLeaseHolderIdx = i
			minLoad = prevAssignedRanges
		}
	}
	replicas.Swap(0, bestLeaseHolderIdx)
	return replicas[0], replicas, nil
}

// writeLeaseHolderToCache resolves the lease holder of a range by probing the
// replicas in a given order. On success, the lease holder is stored in the
// LeaseHolderCache. Failures are swallowed.
// Probing a replica also the effect that the replica tries to acquire a lease.
// So if there's no active lease for the respective range, this will cause the
// recipient to become the lease holder. In other words, be careful whom you put
// at the head of the replicas list.
func (lr *LeaseHolderResolver) writeLeaseHolderToCache(
	desc *roachpb.RangeDescriptor, replicas kv.ReplicaSlice) {
	// TODO(andrei): implement. Needs a new type of replica admin command.
}

// getRangeDescriptors takes a list of spans are resolves it to a list of
// ranges. Spans need to be disjoint and sorted, and so will the results be.
// !!! The results need to indicate if one range somehow covered multiple spans,
// or the other way around.
func (lr *LeaseHolderResolver) getRangeDescriptors(
	ctx context.Context, spans []roachpb.Span,
) ([]*roachpb.RangeDescriptor, error) {
	var res []*roachpb.RangeDescriptor
	for _, span := range spans {
		descs, err := lr.resolveSpan(ctx, span)
		if err != nil {
			return nil, err
		}
		// The first range returned might be the same as the last one from the
		// previous spans (spans are disjunct and sorted).
		if len(res) > 0 && descs[0].RangeID == res[len(res)-1].RangeID {
			descs = descs[1:]
		}
		res = append(res, descs...)
	}
	return res, nil
}

func (lr *LeaseHolderResolver) resolveSpan(
	ctx context.Context, span roachpb.Span,
) ([]*roachpb.RangeDescriptor, error) {
	var retryOptions retry.Options
	// !!! init the options

	var res []*roachpb.RangeDescriptor
	var desc *roachpb.RangeDescriptor
	needAnother := true
	for needAnother {
		var evictToken *kv.EvictionToken
		var err error
		for r := retry.Start(retryOptions); r.Next(); {
			log.Trace(ctx, "meta descriptor lookup")
			startKey, err := keys.Addr(span.Key)
			if err != nil {
				return nil, err
			}
			var endKey roachpb.RKey
			if len(span.EndKey) != 0 {
				var err error
				endKey, err = keys.Addr(span.EndKey)
				if err != nil {
					return nil, err
				}
			}
			rs := roachpb.RSpan{Key: startKey, EndKey: endKey}
			desc, needAnother, evictToken, err = kv.ResolveKeySpanToFirstDescriptor(
				ctx, lr.rangeCache, rs, evictToken, false /* isReverse */)

			// getDescriptors may fail retryably if, for example, the first
			// range isn't available via Gossip. Assume that all errors at
			// this level are retryable. Non-retryable errors would be for
			// things like malformed requests which we should have checked
			// for before reaching this point.
			// !!! turn this into a comment on ResolveKeySpanToFirstDescriptor.
			if err != nil {
				log.VTracef(1, ctx, "range descriptor lookup failed: %s", err.Error())
				continue
			} else {
				log.VTracef(2, ctx, "looked up range descriptor")
				res = append(res, desc)
				break
			}
		}
		if err != nil {
			return nil, err
		}
	}
	return res, nil
}

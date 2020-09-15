// Copyright 2014 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

package kvcoord

import (
	"bytes"
	"context"
	"fmt"
	"strconv"
	"strings"
	"time"

	"github.com/biogo/store/llrb"
	"github.com/cockroachdb/cockroach/pkg/keys"
	"github.com/cockroachdb/cockroach/pkg/kv/kvbase"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/settings/cluster"
	"github.com/cockroachdb/cockroach/pkg/util"
	"github.com/cockroachdb/cockroach/pkg/util/cache"
	"github.com/cockroachdb/cockroach/pkg/util/contextutil"
	"github.com/cockroachdb/cockroach/pkg/util/grpcutil"
	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/cockroachdb/cockroach/pkg/util/stop"
	"github.com/cockroachdb/cockroach/pkg/util/syncutil"
	"github.com/cockroachdb/cockroach/pkg/util/syncutil/singleflight"
	"github.com/cockroachdb/cockroach/pkg/util/tracing"
	"github.com/cockroachdb/errors"
	"github.com/cockroachdb/logtags"
	"github.com/opentracing/opentracing-go"
)

// rangeCacheKey is the key type used to store and sort values in the
// RangeCache.
type rangeCacheKey roachpb.RKey

var minCacheKey interface{} = rangeCacheKey(roachpb.RKeyMin)

func (a rangeCacheKey) String() string {
	return roachpb.Key(a).String()
}

// Compare implements the llrb.Comparable interface for rangeCacheKey, so that
// it can be used as a key for util.OrderedCache.
func (a rangeCacheKey) Compare(b llrb.Comparable) int {
	return bytes.Compare(a, b.(rangeCacheKey))
}

// RangeDescriptorDB is a type which can query range descriptors from an
// underlying datastore. This interface is used by RangeDescriptorCache to
// initially retrieve information which will be cached.
type RangeDescriptorDB interface {
	// RangeLookup takes a key to look up descriptors for. Two slices of range
	// descriptors are returned. The first of these slices holds descriptors
	// whose [startKey,endKey) spans contain the given key (possibly from
	// intents), and the second holds prefetched adjacent descriptors.
	RangeLookup(
		ctx context.Context, key roachpb.RKey, useReverseScan bool,
	) ([]roachpb.RangeDescriptor, []roachpb.RangeDescriptor, error)

	// FirstRange returns the descriptor for the first Range. This is the
	// Range containing all meta1 entries.
	// TODO(nvanbenschoten): pull this detail in DistSender.
	FirstRange() (*roachpb.RangeDescriptor, error)
}

// RangeDescriptorCache is used to retrieve range descriptors for
// arbitrary keys. Descriptors are initially queried from storage
// using a RangeDescriptorDB, but are cached for subsequent lookups.
type RangeDescriptorCache struct {
	st      *cluster.Settings
	stopper *stop.Stopper
	// RangeDescriptorDB is used to retrieve range descriptors from the
	// database, which will be cached by this structure.
	db RangeDescriptorDB
	// rangeCache caches replica metadata for key ranges. The cache is
	// filled while servicing read and write requests to the key value
	// store.
	rangeCache struct {
		syncutil.RWMutex
		cache *cache.OrderedCache
	}
	// lookupRequests stores all inflight requests retrieving range
	// descriptors from the database. It allows multiple RangeDescriptorDB
	// lookup requests for the same inferred range descriptor to be
	// multiplexed onto the same database lookup. See makeLookupRequestKey
	// for details on this inference.
	lookupRequests singleflight.Group

	// coalesced, if not nil, is sent on every time a request is coalesced onto
	// another in-flight one. Used by tests to block until a lookup request is
	// blocked on the single-flight querying the db.
	coalesced chan struct{}
}

// RangeDescriptorCache implements the kvbase interface.
var _ kvbase.RangeDescriptorCache = (*RangeDescriptorCache)(nil)

// makeLookupRequestKey constructs a key for the lookupRequest group with the
// goal of mapping all requests which are inferred to be looking for the same
// descriptor onto the same request key to establish request coalescing.
//
// If the key is part of a descriptor that we previously had cached (but the
// cache entry is stale), we use that previous descriptor to coalesce all
// requests for keys within it into a single request. Namely, there are three
// possible events that may have happened causing our cache to be stale. For
// each of these, we try to coalesce all requests that will end up on the same
// range post-event together.
// - Split:  for a split, only the right half of the split will attempt to evict
//           the stale descriptor because only the right half will be sending to
//           the wrong range. Once this stale descriptor is evicted, keys from
//           both halves of the split will miss the cache. Because both sides of
//           the split will now map to the same EvictionToken, it is important to
//           use EvictAndReplace if possible to insert one of the two new descriptors.
//           This way, no requests to that descriptor will ever miss the cache and
//           risk being coalesced into the other request. If this is not possible,
//           the lookup will still work, but it will require multiple lookups, which
//           will be launched in series when requests find that their desired key
//           is outside of the returned descriptor.
// - Merges: for a merge, the left half of the merge will never notice. The right
//           half of the merge will suddenly find its descriptor to be stale, so
//           it will evict and lookup the new descriptor. We set the key to hash
//           to the start of the stale descriptor for lookup requests to the right
//           half of the merge so that all requests will be coalesced to the same
//           lookupRequest.
// - Rebal:  for a rebalance, the entire descriptor will suddenly go stale and
//           requests to it will evict the descriptor. We set the key to hash to
//           the start of the stale descriptor for lookup requests to the rebalanced
//           descriptor so that all requests will be coalesced to the same lookupRequest.
//
// Note that the above description assumes that useReverseScan is false for simplicity.
// If useReverseScan is true, we need to use the end key of the stale descriptor instead.
func makeLookupRequestKey(
	key roachpb.RKey, prevDesc *roachpb.RangeDescriptor, useReverseScan bool,
) string {
	var ret strings.Builder
	// We only want meta1, meta2, user range lookups to be coalesced with other
	// meta1, meta2, user range lookups, respectively. Otherwise, deadlocks could
	// happen due to singleflight. If the range lookup is in a meta range, we
	// prefix the request key with the corresponding meta prefix to disambiguate
	// the different lookups.
	if key.AsRawKey().Compare(keys.Meta1KeyMax) < 0 {
		ret.Write(keys.Meta1Prefix)
	} else if key.AsRawKey().Compare(keys.Meta2KeyMax) < 0 {
		ret.Write(keys.Meta2Prefix)
	}
	if prevDesc != nil {
		if useReverseScan {
			key = prevDesc.EndKey
		} else {
			key = prevDesc.StartKey
		}
	}
	ret.Write(key)
	ret.WriteString(":")
	ret.WriteString(strconv.FormatBool(useReverseScan))
	// Add the generation of the previous descriptor to the lookup request key to
	// decrease the number of lookups in the rare double split case. Suppose we
	// have a range [a, e) that gets split into [a, c) and [c, e). The requests
	// on [c, e) will fail and will have to retry the lookup. If [a, c) gets
	// split again into [a, b) and [b, c), we don't want to the requests on [a,
	// b) to be coalesced with the retried requests on [c, e). To distinguish the
	// two cases, we can use the generation of the previous descriptor.
	if prevDesc != nil {
		ret.WriteString(":")
		ret.WriteString(prevDesc.Generation.String())
	}
	return ret.String()
}

// NewRangeDescriptorCache returns a new RangeDescriptorCache which
// uses the given RangeDescriptorDB as the underlying source of range
// descriptors.
func NewRangeDescriptorCache(
	st *cluster.Settings, db RangeDescriptorDB, size func() int64, stopper *stop.Stopper,
) *RangeDescriptorCache {
	rdc := &RangeDescriptorCache{st: st, db: db, stopper: stopper}
	rdc.rangeCache.cache = cache.NewOrderedCache(cache.Config{
		Policy: cache.CacheLRU,
		ShouldEvict: func(n int, _, _ interface{}) bool {
			return int64(n) > size()
		},
	})
	return rdc
}

func (rdc *RangeDescriptorCache) String() string {
	rdc.rangeCache.RLock()
	defer rdc.rangeCache.RUnlock()
	return rdc.stringLocked()
}

func (rdc *RangeDescriptorCache) stringLocked() string {
	var buf strings.Builder
	rdc.rangeCache.cache.Do(func(k, v interface{}) bool {
		fmt.Fprintf(&buf, "key=%s desc=%+v\n", roachpb.Key(k.(rangeCacheKey)), v)
		return false
	})
	return buf.String()
}

// EvictionToken holds eviction state between calls to Lookup.
type EvictionToken struct {
	// rdc is the cache that produced this token - and that will be modified by
	// Evict().
	rdc *RangeDescriptorCache

	// entry is the cache entry that this EvictionToken refers to - the entry that
	// Evict() will evict from rdc.
	entry *rangeCacheEntry
	// speculativeDesc, if not nil, is the descriptor that should replace desc if
	// desc proves to be stale - i.e. speculativeDesc is inserted in the cache
	// automatically by Evict(). This is used when the range descriptor lookup
	// that populated the cache returned an intent in addition to the current
	// descriptor value. The idea is that, if the range lookup was performed in
	// the middle of a split or a merge and it's seen an intent, it's likely that
	// the intent will get committed soon and so the client should use it if the
	// previous version proves stale. This mechanism also has a role for resolving
	// intents for the split transactions itself where, immediately after the
	// split's txn record is committed, an intent is the only correct copy of the
	// LHS' descriptor.
	//
	// TODO(andrei): It's weird that speculativeDesc hangs from an EvictionToken,
	// instead of from a cache entry. Hanging from a particular token, only one
	// actor has the opportunity to use this speculativeDesc; if another actor
	// races to evict the respective cache entry and wins, speculativeDesc becomes
	// useless.
	speculativeDesc *roachpb.RangeDescriptor
}

func (rdc *RangeDescriptorCache) makeEvictionToken(
	entry *rangeCacheEntry, speculativeDesc *roachpb.RangeDescriptor,
) EvictionToken {
	if speculativeDesc != nil {
		// speculativeDesc comes from intents. Being uncommitted, it is speculative.
		// We reset its generation to indicate this fact and allow it to be easily
		// overwritten. Putting a speculative descriptor in the cache with a
		// generation might make it hard for the real descriptor with the same
		// generation to overwrite it, in case the speculation fails.
		nextCpy := *speculativeDesc
		nextCpy.Generation = 0
		speculativeDesc = &nextCpy
	}
	return EvictionToken{
		rdc:             rdc,
		entry:           entry,
		speculativeDesc: speculativeDesc,
	}
}

func (et EvictionToken) String() string {
	if et.Empty() {
		return "<empty>"
	}
	return fmt.Sprintf("entry:%s spec desc: %s", et.entry, et.speculativeDesc.String())
}

// Empty returns true if the token is not populated.
func (et EvictionToken) Empty() bool {
	return et == (EvictionToken{})
}

// Desc returns the RangeDescriptor that was retrieved from the cache. The
// result is to be considered immutable.
//
// Note that the returned descriptor might have Generation = 0. This means that
// the descriptor is speculative; it is not know to have committed.
func (et EvictionToken) Desc() *roachpb.RangeDescriptor {
	if et.Empty() {
		return nil
	}
	return et.entry.Desc()
}

// Leaseholder returns the cached leaseholder. If the cache didn't have any
// lease information, returns nil. The result is to be considered immutable.
//
// If a leaseholder is returned, it will correspond to one of the replicas in
// et.Desc().
func (et EvictionToken) Leaseholder() *roachpb.ReplicaDescriptor {
	if et.Empty() {
		return nil
	}
	return et.entry.Leaseholder()
}

// LeaseSeq returns the sequence of the cached lease. If no lease is cached, or
// the cached lease is speculative, 0 is returned.
func (et EvictionToken) LeaseSeq() roachpb.LeaseSequence {
	if et.Empty() {
		panic("invalid LeaseSeq() call on empty EvictionToken")
	}
	return et.entry.lease.Sequence
}

// UpdateLease updates the leaseholder for the token's cache entry to the
// specified lease, and returns an updated EvictionToken, tied to the new cache
// entry.
//
// The bool retval is true if the requested update was performed (i.e. the
// passed-in lease was compatible with the descriptor and more recent than the
// cached lease).
//
// UpdateLease also acts as a synchronization point between the caller and the
// RangeDescriptorCache. In the spirit of a Compare-And-Swap operation (but
// unfortunately not quite as simple), it returns updated information (besides
// the lease) from the cache in case the EvictionToken was no longer up to date
// with the cache entry from whence it came.
//
// The updated token might have a newer descriptor than before and/or a newer
// lease than the one passed-in - in case the cache already had a more recent
// entry. The returned entry has a descriptor compatible to the original one
// (same range id and key span).
//
// If the passed-in lease is incompatible with the cached descriptor (i.e. the
// leaseholder is not a replica in the cached descriptor), then the existing
// entry is evicted and an empty token is returned. The caller should take an
// empty returned token to mean that the information it was working with is too
// stale to be useful, and it should use a range iterator again to get an
// updated cache entry.
//
// It's legal to pass in a lease with a zero Sequence; it will be treated as a
// speculative lease and considered newer than any existing lease (and then in
// turn will be overridden by any subsequent update).
func (et EvictionToken) UpdateLease(
	ctx context.Context, lease *roachpb.Lease,
) (EvictionToken, bool) {
	// If the lease we've been given is older than what the cache entry already has,
	// then short-circuit and don't evict the current entry.
	{
		shouldUpdate, _ := et.entry.updateLease(lease)
		if !shouldUpdate {
			return et, false
		}
	}
	return et.updateLeaseInternal(ctx, lease)
}

func (et EvictionToken) updateLeaseInternal(
	ctx context.Context, lease *roachpb.Lease,
) (EvictionToken, bool) {
	// Notes for what follows: We can't simply update the cache
	// entry in place since entries are immutable. So, we're going to evict the
	// old cache entry and insert a new one, and then change this eviction token
	// to point to the new entry. Note that the eviction token itself does not
	// count as having been evicted (we don't use et.evictOnce), and so the caller
	// can continue using it.
	log.VEventf(ctx, 2, "!!! updating lease: entry: %s, lease: %s", et.entry, lease)

	et.rdc.rangeCache.Lock()
	defer et.rdc.rangeCache.Unlock()

	// Evict our entry and, in the process, see if the cache has a more recent
	// entry.
	evicted, curEntry := et.rdc.evictLocked(ctx, et.entry)
	log.VEventf(ctx, 2, "!!! updating lease: evicted: %t, curEntry: %s", evicted, curEntry)
	if !evicted && curEntry == nil {
		// The cache doesn't know what range we're talking about. We must have very
		// stale info.
		return EvictionToken{}, false
	}
	// If we got a more recent entry, that's the entry we'll try to update.
	if !evicted {
		et.entry = curEntry
	}

	shouldUpdate, updatedEntry := et.entry.updateLease(lease)
	log.VEventf(ctx, 2, "!!! updating lease: should update: %t; updatedEntry: %s", shouldUpdate, updatedEntry)
	if !shouldUpdate {
		log.VEventf(ctx, 2, "!!! updating lease: new lease is not newer; new: %s existing: %s", lease, et.entry.lease)
		return et, false
	}
	// Replace the entry.
	if !evicted {
		log.VEventf(ctx, 2, "!!! updating lease: evicted: %t, entry: %s", evicted, et.entry)
		et.rdc.mustEvictLocked(ctx, et.entry)
	}
	// updatedEntry == nil means that lease is incompatible with the descriptor in
	// the entry. The descriptor must be stale (and we evicted it), but we have no
	// replacement for it.
	if updatedEntry == nil {
		return EvictionToken{}, false
	}
	et.entry = updatedEntry
	log.VEventf(ctx, 2, "!!! updating lease: about to insert: %s (%p = %p)", updatedEntry, updatedEntry, et.entry)
	if et.entry != updatedEntry {
		panic("!!!")
	}
	et.rdc.mustInsertLocked(ctx, updatedEntry)
	return et, true
}

// UpdateLeaseholder is like UpdateLease(), but it only takes a leaseholder, not
// a full lease. This is called when a likely leaseholder is known, but not a
// full lease. The lease we'll insert into the cache will be considered
// "speculative".
func (et EvictionToken) UpdateLeaseholder(
	ctx context.Context, lh roachpb.ReplicaDescriptor,
) EvictionToken {
	// Notice that we don't initialize Lease.Sequence, which will make
	// entry.LeaseSpeculative() return true.
	et, _ /* ok */ = et.updateLeaseInternal(ctx, &roachpb.Lease{Replica: lh})
	return et
}

// ClearLease evicts information about the current lease from the cache, if the
// cache entry referenced by the token is still in the cache.
//
// Similarly to UpdateLease(), ClearLease() acts as a synchronization point
// between the caller and the RangeDescriptorCache. The caller might get an
// updated token (besides the lease).
//
// Returns the updated EvictionToken. Note that this updated token might have a
// newer descriptor than before and/or still have a lease in it - in case the
// cache already had a more recent entry. The returned descriptor is compatible
// (same range id and key span) to the original one. Returns an empty token if
// the cache has a more recent entry, but the current descriptor is
// incompatible. Callers should interpret such a response as a signal that they
// should use a range iterator again to get updated ranges.
func (et EvictionToken) ClearLease(ctx context.Context) EvictionToken {
	et.rdc.rangeCache.Lock()
	defer et.rdc.rangeCache.Unlock()

	if et.entry.lease.Empty() {
		log.Fatalf(ctx, "attempting to clear lease from cache entry without lease")
	}

	var replacementEntry *rangeCacheEntry
	ok, newerEntry := et.rdc.evictLocked(ctx, et.entry)
	if ok {
		// This is the happy case: our entry was in the cache and we just evicted
		// it. We'll now insert a replacement without a lease.
		replacementEntry = &rangeCacheEntry{
			desc: et.entry.desc,
			// No lease.
			lease: roachpb.Lease{},
		}
	} else if newerEntry != nil {
		// We're trying to clear a lease, but we find out that the cache might have
		// newer version of the entry. If that newer version has a different lease,
		// we don't clear anything. Note that we look at the lease's replica, not
		// sequence; the idea is that this clearing of a lease comes in response to
		// trying the known leaseholder and failing - so it's a particular node that
		// we have a problem with, not a particular lease (i.e. we want to evict
		// even a newer lease, but with the same leaseholder).
		if newerEntry.lease.Replica != et.entry.lease.Replica {
			et.entry = newerEntry
			return et
		}
		// The newer entry has the same lease, so we still want to clear it. We
		// replace the entry, but keep the possibly newer descriptor.
		et.rdc.mustEvictLocked(ctx, newerEntry)
		replacementEntry = &rangeCacheEntry{
			desc:  *newerEntry.Desc(),
			lease: roachpb.Lease{},
		}
	} else {
		// The cache doesn't have info about this range any more, or the range keys
		// have changed. Let's bail, it's unclear if there's anything to be updated.
		return EvictionToken{}
	}

	if replacementEntry == nil {
		log.Fatalf(ctx, "programming error; we should have a replacement")
	}
	et.entry = replacementEntry
	et.rdc.mustInsertLocked(ctx, et.entry)
	return et
}

func descsCompatible(a, b *roachpb.RangeDescriptor) bool {
	return (a.RangeID == b.RangeID) && (a.RSpan().Equal(b.RSpan()))
}

// Evict instructs the EvictionToken to evict the RangeDescriptor it was created
// with from the RangeDescriptorCache.
func (et EvictionToken) Evict(ctx context.Context) {
	et.EvictAndReplace(ctx)
}

// EvictAndReplace instructs the EvictionToken to evict the RangeDescriptor it was
// created with from the RangeDescriptorCache. It also allows the user to provide
// new RangeDescriptors to insert into the cache, all atomically. When called without
// arguments, EvictAndReplace will behave the same as Evict.
func (et EvictionToken) EvictAndReplace(ctx context.Context, newDescs ...roachpb.RangeInfo) {
	et.rdc.rangeCache.Lock()
	defer et.rdc.rangeCache.Unlock()
	log.VEventf(ctx, 2, "EvictAndReplace %s. newDescs: %s. speculative desc: %s", et.entry, newDescs, et.speculativeDesc)
	et.rdc.evictLocked(ctx, et.entry)
	if len(newDescs) > 0 {
		log.Eventf(ctx, "evicting cached range descriptor with %d replacements", len(newDescs))
		et.rdc.insertLocked(ctx, newDescs...)
	} else if et.speculativeDesc != nil {
		log.Eventf(ctx, "evicting cached range descriptor with replacement from token")
		et.rdc.insertLocked(ctx, roachpb.RangeInfo{
			Desc: *et.speculativeDesc,
			// We don't know anything about the new lease.
			Lease: roachpb.Lease{},
		})
	} else {
		log.Eventf(ctx, "evicting cached range descriptor")
	}
}

// LookupWithEvictionToken attempts to locate a descriptor, and possibly also a
// lease) for the range containing the given key. This is done by first trying
// the cache, and then querying the two-level lookup table of range descriptors
// which cockroach maintains. The function should be provided with an
// EvictionToken if one was acquired from this function on a previous lookup. If
// not, a nil EvictionToken can be provided.
//
// This method first looks up the specified key in the first level of
// range metadata, which returns the location of the key within the
// second level of range metadata. This second level location is then
// queried to retrieve a descriptor for the range where the key's
// value resides. Range descriptors retrieved during each search are
// cached for subsequent lookups.
//
// The returned EvictionToken contains the descriptor and, possibly, the lease.
// It can also be used to evict information from the cache if it's found to be
// stale.
func (rdc *RangeDescriptorCache) LookupWithEvictionToken(
	ctx context.Context, key roachpb.RKey, evictToken EvictionToken, useReverseScan bool,
) (EvictionToken, error) {
	tok, err := rdc.lookupInternal(ctx, key, evictToken, useReverseScan)
	if err != nil {
		return EvictionToken{}, err
	}
	return tok, nil
}

// Lookup presents a simpler interface for looking up a
// RangeDescriptor for a key without the eviction tokens or scan direction
// control of LookupWithEvictionToken. This method is exported
// to lower level clients through the kvbase.RangeDescriptorCache interface.
func (rdc *RangeDescriptorCache) Lookup(
	ctx context.Context, key roachpb.RKey,
) (kvbase.RangeCacheEntry, error) {
	tok, err := rdc.lookupInternal(
		ctx, key, EvictionToken{}, false /* useReverseScan */)
	if err != nil {
		return nil, err
	}
	return tok.entry, nil
}

// GetCachedOverlapping returns all the cached entries which overlap a given
// span [Key, EndKey). The results are sorted ascendingly.
func (rdc *RangeDescriptorCache) GetCachedOverlapping(
	ctx context.Context, span roachpb.RSpan,
) []kvbase.RangeCacheEntry {
	rdc.rangeCache.RLock()
	defer rdc.rangeCache.RUnlock()
	rawEntries := rdc.getCachedOverlappingRLocked(ctx, span)
	entries := make([]kvbase.RangeCacheEntry, len(rawEntries))
	for i, e := range rawEntries {
		entries[i] = rdc.getValue(e)
	}
	return entries
}

func (rdc *RangeDescriptorCache) getCachedOverlappingRLocked(
	ctx context.Context, span roachpb.RSpan,
) []*cache.Entry {
	var res []*cache.Entry
	rdc.rangeCache.cache.DoRangeReverseEntry(func(e *cache.Entry) (exit bool) {
		desc := rdc.getValue(e).Desc()
		if desc.StartKey.Equal(span.EndKey) {
			// Skip over descriptor starting at the end key, who'd supposed to be exclusive.
			return false
		}
		// Stop when we get to a lower range.
		if desc.EndKey.Compare(span.Key) <= 0 {
			return true
		}
		res = append(res, e)
		return false // continue iterating
	}, rangeCacheKey(span.EndKey), minCacheKey)
	// Invert the results so the get sorted ascendingly.
	for i, j := 0, len(res)-1; i < j; i, j = i+1, j-1 {
		res[i], res[j] = res[j], res[i]
	}
	return res
}

// lookupInternal is called from Lookup or from tests.
//
// If a WaitGroup is supplied, it is signaled when the request is
// added to the inflight request map (with or without merging) or the
// function finishes. Used for testing.
func (rdc *RangeDescriptorCache) lookupInternal(
	ctx context.Context, key roachpb.RKey, evictToken EvictionToken, useReverseScan bool,
) (EvictionToken, error) {
	// Retry while we're hitting lookupCoalescingErrors.
	for {
		newToken, err := rdc.tryLookup(ctx, key, evictToken, useReverseScan)
		if errors.HasType(err, (lookupCoalescingError{})) {
			log.VEventf(ctx, 2, "bad lookup coalescing; retrying: %s", err)
			continue
		}
		if err != nil {
			return EvictionToken{}, err
		}
		return newToken, nil
	}
}

// lookupCoalescingError is returned by tryLookup() when the
// descriptor database lookup failed because this request was grouped with
// another request for another key, and the grouping proved bad since that other
// request returned a descriptor that doesn't cover our request. The lookup
// should be retried.
type lookupCoalescingError struct {
	// key is the key whose range was being looked-up.
	key       roachpb.RKey
	wrongDesc *roachpb.RangeDescriptor
}

func (e lookupCoalescingError) Error() string {
	return fmt.Sprintf("key %q not contained in range lookup's "+
		"resulting descriptor %v", e.key, e.wrongDesc)
}

func newLookupCoalescingError(key roachpb.RKey, wrongDesc *roachpb.RangeDescriptor) error {
	return lookupCoalescingError{
		key:       key,
		wrongDesc: wrongDesc,
	}
}

// tryLookup can return a lookupCoalescingError.
func (rdc *RangeDescriptorCache) tryLookup(
	ctx context.Context, key roachpb.RKey, evictToken EvictionToken, useReverseScan bool,
) (EvictionToken, error) {
	rdc.rangeCache.RLock()
	if entry, _ := rdc.getCachedRLocked(ctx, key, useReverseScan); entry != nil {
		log.VEventf(ctx, 2, "!!! range cache hit for key: %s. entry: %s (%p)", key, entry, entry)
		rdc.rangeCache.RUnlock()
		returnToken := rdc.makeEvictionToken(entry, nil /* nextDesc */)
		return returnToken, nil
	}

	if log.V(2) {
		log.Infof(ctx, "lookup range descriptor: key=%s (reverse: %t)", key, useReverseScan)
	}

	var prevDesc *roachpb.RangeDescriptor
	if !evictToken.Empty() {
		prevDesc = evictToken.Desc()
	}
	requestKey := makeLookupRequestKey(key, prevDesc, useReverseScan)
	resC, leader := rdc.lookupRequests.DoChan(requestKey, func() (interface{}, error) {
		var lookupRes EvictionToken
		if err := rdc.stopper.RunTaskWithErr(ctx, "rangecache: range lookup", func(ctx context.Context) error {
			ctx, reqSpan := tracing.ForkCtxSpan(ctx, "range lookup")
			defer tracing.FinishSpan(reqSpan)
			// Clear the context's cancelation. This request services potentially many
			// callers waiting for its result, and using the flight's leader's
			// cancelation doesn't make sense.
			ctx = logtags.WithTags(context.Background(), logtags.FromContext(ctx))
			ctx = opentracing.ContextWithSpan(ctx, reqSpan)

			// Since we don't inherit any other cancelation, let's put in a generous
			// timeout as some protection against unavailable meta ranges.
			var rs, preRs []roachpb.RangeDescriptor
			if err := contextutil.RunWithTimeout(ctx, "range lookup", 10*time.Second,
				func(ctx context.Context) error {
					var err error
					rs, preRs, err = rdc.performRangeLookup(ctx, key, useReverseScan)
					return err
				}); err != nil {
				return err
			}

			switch {
			case len(rs) == 0:
				return fmt.Errorf("no range descriptors returned for %s", key)
			case len(rs) > 2:
				panic(fmt.Sprintf("more than 2 matching range descriptors returned for %s: %v", key, rs))
			}

			// We want to be assured that all goroutines which experienced a cache miss
			// have joined our in-flight request, and all others will experience a
			// cache hit. This requires atomicity across cache population and
			// notification, hence this exclusive lock.
			rdc.rangeCache.Lock()
			defer rdc.rangeCache.Unlock()

			// Insert the descriptor and the prefetched ones. We don't insert rs[1]
			// (if any), since it overlaps with rs[0]; rs[1] will be handled by
			// rs[0]'s eviction token. Note that ranges for which the cache has more
			// up-to-date information will not be clobbered - for example ranges for
			// which the cache has the prefetched descriptor already plus a lease.
			newEntries := make([]*rangeCacheEntry, len(preRs)+1)
			newEntries[0] = &rangeCacheEntry{
				desc: rs[0],
				// We don't have any lease information.
				lease: roachpb.Lease{},
			}
			for i, preR := range preRs {
				newEntries[i+1] = &rangeCacheEntry{desc: preR}
			}
			insertedEntries := rdc.insertLockedInner(ctx, newEntries)
			// entry corresponds to rs[0], which is the descriptor covering the key
			// we're interested in.
			entry := insertedEntries[0]
			// There's 3 cases here:
			// 1. We succeeded in inserting rs[0].
			// 2. We didn't succeed in inserting rs[0], but insertedEntries[0] still was non-nil. This
			// means that the cache had a newer version of the descriptor. In that
			// case it's all good, we just pretend that that's the version we were inserting; we put it in our
			// token and continue.
			// 3. insertedEntries[0] is nil. The cache has newer entries in them and
			// they're not compatible with the descriptor we were trying to insert.
			// This case should be rare, since very recently (before starting the
			// singleflight), the cache didn't have any entry for the requested key.
			// We'll continue with the stale rs[0]; we'll pretend that we did by
			// putting a dummy entry in the eviction token. This will make eviction
			// no-ops (which makes sense - there'll be nothing to evict since we
			// didn't insert anything).
			// TODO(andrei): It'd be better to retry the cache/database lookup in case 3.
			if entry == nil {
				entry = &rangeCacheEntry{
					desc:  rs[0],
					lease: roachpb.Lease{},
				}
			}
			if len(rs) == 1 {
				lookupRes = rdc.makeEvictionToken(entry, nil /* nextDesc */)
			} else {
				lookupRes = rdc.makeEvictionToken(entry, &rs[1] /* nextDesc */)
			}
			return nil
		}); err != nil {
			return nil, err
		}
		return lookupRes, nil
	})

	// We must use DoChan above so that we can always unlock this mutex. This must
	// be done *after* the request has been added to the lookupRequests group, or
	// we risk it racing with an inflight request.
	rdc.rangeCache.RUnlock()

	if !leader {
		log.VEvent(ctx, 2, "coalesced range lookup request onto in-flight one")
		if rdc.coalesced != nil {
			rdc.coalesced <- struct{}{}
		}
	}

	// Wait for the inflight request.
	var res singleflight.Result
	select {
	case res = <-resC:
	case <-ctx.Done():
		return EvictionToken{}, errors.Wrap(ctx.Err(), "aborted during range descriptor lookup")
	}

	var s string
	if res.Err != nil {
		s = res.Err.Error()
	} else {
		s = res.Val.(EvictionToken).entry.String()
	}
	if res.Shared {
		log.Eventf(ctx, "looked up range descriptor with shared request: %s", s)
	} else {
		log.Eventf(ctx, "looked up range descriptor: %s", s)
	}
	if res.Err != nil {
		return EvictionToken{}, res.Err
	}

	// We might get a descriptor that doesn't contain the key we're looking for
	// because of bad grouping of requests. For example, say we had a stale
	// [a-z) in the cache who's info is passed into this function as evictToken.
	// In the meantime the range has been split to [a-m),[m-z). A request for "a"
	// will be coalesced with a request for "m" in the singleflight, above, but
	// one of them will get a wrong results. We return an error that will trigger
	// a retry at a higher level inside the cache. Note that the retry might find
	// the descriptor it's looking for in the cache if it was pre-fetched by the
	// original lookup.
	lookupRes := res.Val.(EvictionToken)
	desc := lookupRes.Desc()
	containsFn := (*roachpb.RangeDescriptor).ContainsKey
	if useReverseScan {
		containsFn = (*roachpb.RangeDescriptor).ContainsKeyInverted
	}
	if !containsFn(desc, key) {
		return EvictionToken{}, newLookupCoalescingError(key, desc)
	}
	return lookupRes, nil
}

// performRangeLookup handles delegating the range lookup to the cache's
// RangeDescriptorDB.
func (rdc *RangeDescriptorCache) performRangeLookup(
	ctx context.Context, key roachpb.RKey, useReverseScan bool,
) ([]roachpb.RangeDescriptor, []roachpb.RangeDescriptor, error) {
	// Tag inner operations.
	ctx = logtags.AddTag(ctx, "range-lookup", key)

	// In this case, the requested key is stored in the cluster's first
	// range. Return the first range, which is always gossiped and not
	// queried from the datastore.
	if keys.RangeMetaKey(key).Equal(roachpb.RKeyMin) {
		desc, err := rdc.db.FirstRange()
		if err != nil {
			return nil, nil, err
		}
		return []roachpb.RangeDescriptor{*desc}, nil, nil
	}

	return rdc.db.RangeLookup(ctx, key, useReverseScan)
}

// Clear clears all RangeDescriptors from the RangeDescriptorCache.
func (rdc *RangeDescriptorCache) Clear() {
	rdc.rangeCache.Lock()
	defer rdc.rangeCache.Unlock()
	rdc.rangeCache.cache.Clear()
}

// EvictByKey evicts the descriptor containing the given key, if any.
//
// Returns true if a descriptor was evicted.
func (rdc *RangeDescriptorCache) EvictByKey(ctx context.Context, descKey roachpb.RKey) bool {
	rdc.rangeCache.Lock()
	defer rdc.rangeCache.Unlock()

	cachedDesc, entry := rdc.getCachedRLocked(ctx, descKey, false /* inverted */)
	if cachedDesc == nil {
		return false
	}
	// !!! log.VEventf(ctx, 2, "evict cached descriptor: %s", cachedDesc)
	log.VEventf(ctx, 2, "evict cached descriptor: %s (%p)", cachedDesc, rdc.getValue(entry))
	rdc.rangeCache.cache.DelEntry(entry)
	return true
}

// evictLocked evicts entry from the cache. If entry is not in the cache
// (according to pointer equality), the cache is not touched. The caller needs
// to holds a write lock on rdc.rangeCache.
//
// entry must have come from the cache on a previous lookup.
//
// Returns true if the entry was evicted from the cache. If false is returned,
// but the cache has an entry that's "compatible" (same range id and key span)
// and newer, that entry is returned. The caller can use this returned entry as
// more recent data than the version it was trying to evict.
func (rdc *RangeDescriptorCache) evictLocked(
	ctx context.Context, entry *rangeCacheEntry,
) (ok bool, updatedEntry *rangeCacheEntry) {
	cachedEntry, rawEntry := rdc.getCachedRLocked(ctx, entry.desc.StartKey, false /* inverted */)
	if cachedEntry != entry {
		if cachedEntry != nil && descsCompatible(cachedEntry.Desc(), entry.Desc()) {
			log.VEventf(ctx, 2, "!!! evictLocked not evicting because cache has newer entry. entry: %s (%p) newer: %s (%p)",
				entry, entry, cachedEntry, cachedEntry)
			return false, cachedEntry
		}
		log.VEventf(ctx, 2, "!!! evictLocked not evicting because cache has nil or incompatible entry. entry: %s newer: %s",
			entry, cachedEntry)
		return false, nil
	}

	// !!! log.VEventf(ctx, 2, "evict cached descriptor: desc=%s", cachedEntry)
	log.VEventf(ctx, 2, "evict cached descriptor: desc=%s (%p)", cachedEntry, cachedEntry)
	rdc.rangeCache.cache.DelEntry(rawEntry)
	return true, nil
}

// mustEvictLocked is like evictLocked, except it asserts that the eviction was
// successful (i.e. that entry is present in the cache). This is used when we're
// evicting an entry that we just looked up, under the lock.
func (rdc *RangeDescriptorCache) mustEvictLocked(ctx context.Context, entry *rangeCacheEntry) {
	ok, newer := rdc.evictLocked(ctx, entry)
	if !ok {
		log.Fatalf(ctx, "failed to evict %s. newer: %v", entry, newer)
	}
}

// GetCached retrieves the descriptor of the range which contains
// the given key. It returns nil if the descriptor is not found in the cache.
//
// `inverted` determines the behavior at the range boundary: If set to true
// and `key` is the EndKey and StartKey of two adjacent ranges, the first range
// is returned instead of the second (which technically contains the given key).
func (rdc *RangeDescriptorCache) GetCached(
	ctx context.Context, key roachpb.RKey, inverted bool,
) kvbase.RangeCacheEntry {
	rdc.rangeCache.RLock()
	defer rdc.rangeCache.RUnlock()
	entry, _ := rdc.getCachedRLocked(ctx, key, inverted)
	if entry == nil {
		// This return avoids boxing a nil into a non-nil iface.
		return nil
	}
	return kvbase.RangeCacheEntry(entry)
}

// getCachedRLocked is like GetCached, but it assumes that the caller holds a
// read lock on rdc.rangeCache.
//
// In addition to GetCached, it also returns an internal cache Entry that can be
// used for descriptor eviction.
func (rdc *RangeDescriptorCache) getCachedRLocked(
	ctx context.Context, key roachpb.RKey, inverted bool,
) (*rangeCacheEntry, *cache.Entry) {
	// rawEntry will be the range containing key, or the first cached entry around
	// key, in the direction indicated by inverted.
	var rawEntry *cache.Entry
	if !inverted {
		var ok bool
		rawEntry, ok = rdc.rangeCache.cache.FloorEntry(rangeCacheKey(key))
		if !ok {
			return nil, nil
		}
	} else {
		rdc.rangeCache.cache.DoRangeReverseEntry(func(e *cache.Entry) bool {
			startKey := roachpb.RKey(e.Key.(rangeCacheKey))
			if key.Equal(startKey) {
				// DoRangeReverseEntry is inclusive on the higher key. We're iterating
				// backwards and we got a range that starts at key. We're not interested
				// in this range; we're interested in the range before it that ends at
				// key.
				return false // continue iterating
			}
			rawEntry = e
			return true
		}, rangeCacheKey(key), minCacheKey)
		// DoRangeReverseEntry is exclusive on the "to" part, so we need to check
		// manually if there's an entry for RKeyMin.
		if rawEntry == nil {
			rawEntry, _ = rdc.rangeCache.cache.FloorEntry(minCacheKey)
		}
	}

	if rawEntry == nil {
		return nil, nil
	}
	entry := rdc.getValue(rawEntry)

	containsFn := (*roachpb.RangeDescriptor).ContainsKey
	if inverted {
		containsFn = (*roachpb.RangeDescriptor).ContainsKeyInverted
	}

	// Return nil if the key does not belong to the range.
	if !containsFn(entry.Desc(), key) {
		return nil, nil
	}
	log.Infof(ctx, "!!! getCachedRLocked returning entry: %s (%p)", entry, entry)
	return entry, rawEntry
}

// Insert inserts range info into the cache.
//
// This is a no-op for the ranges that already have the same, or newer, info in
// the cache.
func (rdc *RangeDescriptorCache) Insert(ctx context.Context, rs ...roachpb.RangeInfo) {
	rdc.rangeCache.Lock()
	defer rdc.rangeCache.Unlock()
	rdc.insertLocked(ctx, rs...)
}

// mustInsertLocked is like Insert(), but it takes a single RangeInfo and it
// fatals if the entry fails to be inserted. It's used when it's known that
// there's nothing in the cache conflicting with the ent because we've just
// successfully evicted a similar entry.
func (rdc *RangeDescriptorCache) mustInsertLocked(ctx context.Context, ent *rangeCacheEntry) {
	entry := rdc.insertLockedInner(ctx, []*rangeCacheEntry{ent})[0]
	if entry == nil {
		log.Fatalf(ctx, "unexpected failure to insert desc: %s", ent)
	}
	log.VEventf(ctx, 2, "!!! mustInsertLocked returning entry: %s (%p)", entry, entry)
}

// insertLocked is like Insert, but it assumes that the caller holds a write
// lock on rdc.rangeCache. It also returns the inserted cache values, suitable
// for putting in eviction tokens. Any element in the returned array can be nil
// if inserting the respective RangeInfo failed because it was found to be
// stale.
func (rdc *RangeDescriptorCache) insertLocked(
	ctx context.Context, rs ...roachpb.RangeInfo,
) []*rangeCacheEntry {
	entries := make([]*rangeCacheEntry, len(rs))
	for i, r := range rs {
		entries[i] = &rangeCacheEntry{
			desc:  r.Desc,
			lease: r.Lease,
		}
	}
	return rdc.insertLockedInner(ctx, entries)
}

func (rdc *RangeDescriptorCache) insertLockedInner(
	ctx context.Context, rs []*rangeCacheEntry,
) []*rangeCacheEntry {
	// entries will have the same element as rs, except the ones that couldn't be
	// inserted for which the slots will remain nil.
	entries := make([]*rangeCacheEntry, len(rs))
	for i, ent := range rs {
		if !ent.desc.IsInitialized() {
			log.Fatalf(ctx, "inserting uninitialized desc: %s", ent)
		}
		if !ent.lease.Empty() {
			replID := ent.lease.Replica.ReplicaID
			_, ok := ent.desc.GetReplicaDescriptorByID(replID)
			if !ok {
				log.Fatalf(ctx, "leaseholder replicaID: %d not part of descriptor: %s. lease: %s",
					replID, ent.Desc(), ent.Lease())
			}
		}
		// Note: we append the end key of each range to meta records
		// so that calls to rdc.rangeCache.cache.Ceil() for a key will return
		// the correct range.

		// Before adding a new entry, make sure we clear out any
		// pre-existing, overlapping entries which might have been
		// re-inserted due to concurrent range lookups.
		ok, newerEntry := rdc.clearOlderOverlappingLocked(ctx, ent)
		if !ok {
			// The descriptor we tried to insert is already in the cache, or is stale.
			// We might have gotten a newer cache entry, if the descriptor in the
			// cache is similar enough. If that's the case, we'll use it.
			// NB: entries[i] stays nil if newerEntry is nil.
			entries[i] = newerEntry
			continue
		}
		rangeKey := ent.Desc().StartKey
		if log.V(2) {
			log.Infof(ctx, "adding cache entry: value=%s (%p)", ent, ent) // !!! %p
		}
		rdc.rangeCache.cache.Add(rangeCacheKey(rangeKey), ent)
		entries[i] = ent
	}
	return entries
}

func (rdc *RangeDescriptorCache) getValue(entry *cache.Entry) *rangeCacheEntry {
	return entry.Value.(*rangeCacheEntry)
}

func (rdc *RangeDescriptorCache) clearOlderOverlapping(
	ctx context.Context, newEntry *rangeCacheEntry,
) (ok bool, newerEntry *rangeCacheEntry) {
	rdc.rangeCache.Lock()
	defer rdc.rangeCache.Unlock()
	return rdc.clearOlderOverlappingLocked(ctx, newEntry)
}

// clearOlderOverlappingLocked clears any stale cache entries which overlap the
// specified descriptor. Returns true if the clearing succeeds, and false if any
// overlapping newer descriptor is found (or if the descriptor we're trying to
// insert is already in the cache). If false is returned, a cache entry might
// also be returned - a cache entry that's similar (same descriptor range id and
// key span) to the one we were trying to insert, but newer (or identical). Such
// an entry might not exist, in which case false, nil will be returned.
//
// Note that even if false is returned, older descriptors are still cleared from
// the cache.
func (rdc *RangeDescriptorCache) clearOlderOverlappingLocked(
	ctx context.Context, newEntry *rangeCacheEntry,
) (ok bool, newerEntry *rangeCacheEntry) {
	log.VEventf(ctx, 2, "clearing entries overlapping %s", newEntry.Desc())
	newest := true
	var newerFound *rangeCacheEntry
	overlapping := rdc.getCachedOverlappingRLocked(ctx, newEntry.Desc().RSpan())
	for _, e := range overlapping {
		entry := rdc.getValue(e)
		if newEntry.overrides(entry) {
			if log.V(2) {
				// !!! log.Infof(ctx, "clearing overlapping descriptor: key=%s entry=%s", e.Key, rdc.getValue(e))
				log.Infof(ctx, "clearing overlapping descriptor: key=%s entry=%s (%p)", e.Key, rdc.getValue(e), rdc.getValue(e))
			}
			rdc.rangeCache.cache.DelEntry(e)
		} else {
			newest = false
			if descsCompatible(entry.Desc(), newEntry.Desc()) {
				newerFound = entry
				// We've found a similar descriptor in the cache; there can't be any
				// other overlapping ones so let's stop the iteration.
				if len(overlapping) != 1 {
					log.Errorf(ctx, "%s", errors.AssertionFailedf(
						"found compatible descriptor but also got multiple overlapping results. newEntry: %s. overlapping: %s",
						newEntry, overlapping).Error())
				}
			}
		}
	}
	return newest, newerFound
}

// rangeCacheEntry represents one cache entry.
//
// The cache stores *rangeCacheEntry. Entries are immutable: cache lookups
// returns the same *rangeCacheEntry to multiple queriers for efficiency, but
// nobody should modify the lookup result.
type rangeCacheEntry struct {
	// desc is always populated.
	desc roachpb.RangeDescriptor
	// Lease has info on the range's lease. It can be Empty() if no lease
	// information is known. When a lease is known, it is guaranteed that the
	// lease comes from Desc's range id (i.e. we'll never put a lease from another
	// range in here). This allows UpdateLease() to use Lease.Sequence to compare
	// leases. Moreover, the lease will correspond to one of the replicas in Desc.
	lease roachpb.Lease
}

func (e rangeCacheEntry) String() string {
	return fmt.Sprintf("desc:%s, lease:%s", e.Desc(), e.lease)
}

func (e *rangeCacheEntry) Desc() *roachpb.RangeDescriptor {
	return &e.desc
}

func (e *rangeCacheEntry) Leaseholder() *roachpb.ReplicaDescriptor {
	if e.lease.Empty() {
		return nil
	}
	return &e.lease.Replica
}

func (e *rangeCacheEntry) Lease() *roachpb.Lease {
	if e.lease.Empty() {
		return nil
	}
	if e.LeaseSpeculative() {
		return nil
	}
	return &e.lease
}

// DescSpeculative returns true if the descriptor in the entry is "speculative"
// - i.e. it doesn't correspond to a committed value. Such descriptors have been
// inserted in the cache with Generation=0.
func (e *rangeCacheEntry) DescSpeculative() bool {
	return e.desc.Generation == 0
}

// LeaseSpeculative returns true if the lease in the entry is "speculative"
// - i.e. it doesn't correspond to a committed lease. Such leases have been
// inserted in the cache with Sequence=0.
func (e *rangeCacheEntry) LeaseSpeculative() bool {
	if e.lease.Empty() {
		panic(fmt.Sprintf("LeaseSpeculative called on entry with empty lease: %s", e))
	}
	return e.lease.Speculative()
}

// overrides returns true if o should replace e in the cache. It is assumed that
// e's and o'd descriptors overlap (and so they can't co-exist in the cache). A
// newer entry overrides an older entry. What entry is newer is decided based
// the descriptor's generation and, for equal generations, by the lease's
// sequence.
//
// In situations where it can't be determined which entry represents newer
// information, e wins - the assumption is that o is already in the cache and we
// have some reason to believe e should get in the cache instead (generally
// because a server gave us this information recently). Situations where it
// can't be determined what information is newer is when at least one of the
// descriptors is "speculative" (generation=0), or when the lease information is
// "speculative" (sequence=0).
func (e *rangeCacheEntry) overrides(o *rangeCacheEntry) bool {
	if util.RaceEnabled {
		if _, err := e.Desc().RSpan().Intersect(o.Desc()); err != nil {
			panic(fmt.Sprintf("descriptors don't intersect: %s vs %s", e.Desc(), o.Desc()))
		}
	}

	if res := compareEntryDescs(o, e); res != 0 {
		return res < 0
	}

	// Equal descriptor generations. Let's look at the lease sequence.

	// If two RangeDescriptors overlap and have the same Generation, they must
	// be referencing the same range, in which case their lease sequences are
	// comparable.
	if e.Desc().RangeID != o.Desc().RangeID {
		panic(fmt.Sprintf("overlapping descriptors with same gen but different IDs: %s vs %s",
			e.Desc(), o.Desc()))
	}

	return compareEntryLeases(o, e) < 0
}

// compareEntryDescs returns -1, 0 or 1 depending on whether a's descriptor is
// considered older, equal to, or newer than b's.
//
// In case at least one of the descriptors is "speculative", a is considered
// older; this matches the semantics of b.overrides(a).
func compareEntryDescs(a, b *rangeCacheEntry) int {
	if util.RaceEnabled {
		if _, err := a.Desc().RSpan().Intersect(b.Desc()); err != nil {
			panic(fmt.Sprintf("descriptors don't intersect: %s vs %s", a.Desc(), b.Desc()))
		}
	}

	if a.desc.Equal(b.desc) {
		return 0
	}

	if a.DescSpeculative() || b.DescSpeculative() {
		return -1
	}

	if a.Desc().Generation < b.Desc().Generation {
		return -1
	}
	if a.Desc().Generation > b.Desc().Generation {
		return 1
	}
	return 0
}

// compareEntryLeases returns -1, 0 or 1 depending on whether a's lease is
// considered older, equal to, or newer than b's. The descriptors in a and b are
// assumed to be the same.
//
// An empty lease is considered older than any other. In case at least one of
// the leases is "speculative", a is considered older; this matches the
// semantics of b.overrides(a).
func compareEntryLeases(a, b *rangeCacheEntry) int {
	if aEmpty, bEmpty := a.lease.Empty(), b.lease.Empty(); aEmpty || bEmpty {
		if aEmpty && !bEmpty {
			return -1
		}
		if !aEmpty && bEmpty {
			return 1
		}
		return 0
	}

	// A speculative lease always loses; we don't know the sequence number of a
	// speculative lease.
	if a.LeaseSpeculative() || b.LeaseSpeculative() {
		return -1
	}

	if a.Lease().Sequence < b.Lease().Sequence {
		return -1
	}
	if a.Lease().Sequence > b.Lease().Sequence {
		return 1
	}
	return 0
}

// updateLease returns a new rangeCacheEntry with the receiver's descriptor and
// a new lease. The updated retval indicates whether the passed-in lease appears
// to be newer than the lease the entry had before. If updated is returned true,
// the caller should evict the existing entry (the receiver) and replace it with
// newEntry. (true, nil) can be returned meaning that the existing entry should
// be evicted, but there's no replacement that this function can provide; this
// happens when the passed-in lease indicates a leaseholder that's not part of
// the entry's descriptor. The descriptor must be really stale, and the caller
// should read a new version.
//
// If updated=false is returned, then newEntry will be the same as the receiver.
// This means that the passed-in lease is older than the lease already in the
// entry.
//
// If the new leaseholder is not a replica in the descriptor, we assume the
// lease information to be more recent than the entry's descriptor, and we
// return true, nil. The caller should evict the receiver from the cache, but
// it'll have to do extra work to figure out what to insert instead.
func (e *rangeCacheEntry) updateLease(l *roachpb.Lease) (updated bool, newEntry *rangeCacheEntry) {
	// If l is older than what the entry has (or the same), return early.
	//
	// This method handles speculative leases: a new lease with a sequence of 0 is
	// presumed to be newer than anything, and an existing lease with a sequence
	// of 0 is presumed to be older than anything.
	//
	// We handle the case of a lease with the sequence equal to the existing
	// entry, but otherwise different. This results in the new lease updating the
	// entry, because the existing lease might correspond to a proposed lease that
	// a replica returned speculatively while a lease acquisition was in progress.
	if l.Sequence != 0 && e.lease.Sequence != 0 && l.Sequence < e.lease.Sequence {
		return false, e
	}

	if l.Equal(e.Lease()) {
		return false, e
	}

	// Check whether the lease we were given is compatible with the replicas in
	// the descriptor. If it's not, the descriptor must be really stale, and the
	// RangeCacheEntry needs to be evicted.
	_, ok := e.desc.GetReplicaDescriptorByID(l.Replica.ReplicaID)
	if !ok {
		return true, nil
	}

	// TODO(andrei): If the leaseholder is present, but the descriptor lists the
	// replica as a learner, this is a sign of a stale descriptor. I'm not sure
	// what to do about it, though.

	return true, &rangeCacheEntry{
		desc:  e.desc,
		lease: *l,
	}
}

// isRangeLookupErrorRetryable returns whether the provided range lookup error
// can be retried or whether it should be propagated immediately.
func isRangeLookupErrorRetryable(err error) bool {
	// For now, all errors are retryable except authentication errors.
	return !grpcutil.IsAuthenticationError(err)
}

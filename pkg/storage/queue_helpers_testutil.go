// Copyright 2019 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

package storage

import (
	"context"

	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/pkg/errors"
)

// Code in this file is for testing usage only. It is exported only because it
// is called from outside of the package.

func (bq *baseQueue) testingAdd(
	ctx context.Context, repl replicaInQueue, priority float64,
) (bool, error) {
	return bq.addInternal(ctx, repl.Desc(), priority)
}

func forceScanAndProcess(ctx context.Context, s *Store, q *baseQueue) (bool, error) {
	// Check that the system config is available. It is needed by many queues. If
	// it's not available, some queues silently fail to process any replicas,
	// which is undesirable for this method.
	if cfg := s.Gossip().GetSystemConfig(); cfg == nil {
		return false, errors.Errorf("system config not available in gossip")
	}

	anyAction := false
	newStoreReplicaVisitor(s).Visit(func(repl *Replica) bool {
		log.Infof(ctx, "!!! visiting repl: %s - %s", repl, repl.Desc())
		anyAction = q.maybeAdd(ctx, repl, s.cfg.Clock.Now()) || anyAction
		return true
	})

	q.DrainQueue(s.stopper)
	return anyAction, nil
}

func mustForceScanAndProcess(ctx context.Context, s *Store, q *baseQueue) bool {
	anyAction, err := forceScanAndProcess(ctx, s, q)
	if err != nil {
		log.Fatal(ctx, err)
	}
	return anyAction
}

// ForceReplicationScanAndProcess iterates over all ranges and
// enqueues any that need to be replicated.
func (s *Store) ForceReplicationScanAndProcess(ctx context.Context) (bool, error) {
	return forceScanAndProcess(ctx, s, s.replicateQueue.baseQueue)
}

func (s *Store) ForceReplicationScanAndProcessLoop(ctx context.Context) error {
	for i := 0; ; i++ {
		log.Infof(ctx, "ForceReplicationScanAndProcessLoop on stores %s iteration %d", s, i)
		anyAction, err := s.ForceReplicationScanAndProcess(ctx)
		if err != nil {
			return err
		}
		if !anyAction {
			return nil
		}
	}
}

// MustForceReplicaGCScanAndProcess iterates over all ranges and enqueues any that
// may need to be GC'd.
func (s *Store) MustForceReplicaGCScanAndProcess() {
	mustForceScanAndProcess(context.TODO(), s, s.replicaGCQueue.baseQueue)
}

// MustForceMergeScanAndProcess iterates over all ranges and enqueues any that
// may need to be merged.
func (s *Store) MustForceMergeScanAndProcess() {
	mustForceScanAndProcess(context.TODO(), s, s.mergeQueue.baseQueue)
}

// ForceSplitScanAndProcess iterates over all ranges and enqueues any that
// may need to be split.
func (s *Store) ForceSplitScanAndProcess() error {
	_, err := forceScanAndProcess(context.TODO(), s, s.splitQueue.baseQueue)
	return err
}

// MustForceRaftLogScanAndProcess iterates over all ranges and enqueues any that
// need their raft logs truncated and then process each of them.
func (s *Store) MustForceRaftLogScanAndProcess() {
	mustForceScanAndProcess(context.TODO(), s, s.raftLogQueue.baseQueue)
}

// ForceTimeSeriesMaintenanceQueueProcess iterates over all ranges, enqueuing
// any that need time series maintenance, then processes the time series
// maintenance queue.
func (s *Store) ForceTimeSeriesMaintenanceQueueProcess() error {
	_, err := forceScanAndProcess(context.TODO(), s, s.tsMaintenanceQueue.baseQueue)
	return err
}

// ForceRaftSnapshotQueueProcess iterates over all ranges, enqueuing
// any that need raft snapshots, then processes the raft snapshot
// queue.
func (s *Store) ForceRaftSnapshotQueueProcess() error {
	_, err := forceScanAndProcess(context.TODO(), s, s.raftSnapshotQueue.baseQueue)
	return err
}

// ForceConsistencyQueueProcess runs all the ranges through the consistency
// queue.
func (s *Store) ForceConsistencyQueueProcess() error {
	_, err := forceScanAndProcess(context.TODO(), s, s.consistencyQueue.baseQueue)
	return err
}

// The methods below can be used to control a store's queues. Stopping a queue
// is only meant to happen in tests.

func (s *Store) setGCQueueActive(active bool) {
	s.gcQueue.SetDisabled(!active)
}
func (s *Store) setMergeQueueActive(active bool) {
	s.mergeQueue.SetDisabled(!active)
}
func (s *Store) setRaftLogQueueActive(active bool) {
	s.raftLogQueue.SetDisabled(!active)
}
func (s *Store) setReplicaGCQueueActive(active bool) {
	s.replicaGCQueue.SetDisabled(!active)
}

// SetReplicateQueueActive controls the replication queue. Only
// intended for tests.
func (s *Store) SetReplicateQueueActive(active bool) {
	s.replicateQueue.SetDisabled(!active)
}
func (s *Store) setSplitQueueActive(active bool) {
	s.splitQueue.SetDisabled(!active)
}
func (s *Store) setTimeSeriesMaintenanceQueueActive(active bool) {
	s.tsMaintenanceQueue.SetDisabled(!active)
}
func (s *Store) setRaftSnapshotQueueActive(active bool) {
	s.raftSnapshotQueue.SetDisabled(!active)
}
func (s *Store) setConsistencyQueueActive(active bool) {
	s.consistencyQueue.SetDisabled(!active)
}
func (s *Store) setScannerActive(active bool) {
	s.scanner.SetDisabled(!active)
}

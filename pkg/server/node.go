// Copyright 2014 The Cockroach Authors.
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

package server

import (
	"context"
	"fmt"
	"math"
	"net"
	"sort"
	"time"

	"github.com/cockroachdb/cockroach/pkg/base"
	"github.com/cockroachdb/cockroach/pkg/build"
	"github.com/cockroachdb/cockroach/pkg/config"
	"github.com/cockroachdb/cockroach/pkg/gossip"
	"github.com/cockroachdb/cockroach/pkg/internal/client"
	"github.com/cockroachdb/cockroach/pkg/keys"
	"github.com/cockroachdb/cockroach/pkg/kv"
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/server/status"
	"github.com/cockroachdb/cockroach/pkg/settings"
	"github.com/cockroachdb/cockroach/pkg/settings/cluster"
	"github.com/cockroachdb/cockroach/pkg/sql"
	"github.com/cockroachdb/cockroach/pkg/sql/sqlbase"
	"github.com/cockroachdb/cockroach/pkg/storage"
	"github.com/cockroachdb/cockroach/pkg/storage/closedts/container"
	"github.com/cockroachdb/cockroach/pkg/storage/engine"
	"github.com/cockroachdb/cockroach/pkg/util"
	"github.com/cockroachdb/cockroach/pkg/util/grpcutil"
	"github.com/cockroachdb/cockroach/pkg/util/hlc"
	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/cockroachdb/cockroach/pkg/util/log/logtags"
	"github.com/cockroachdb/cockroach/pkg/util/metric"
	"github.com/cockroachdb/cockroach/pkg/util/retry"
	"github.com/cockroachdb/cockroach/pkg/util/stop"
	"github.com/cockroachdb/cockroach/pkg/util/timeutil"
	"github.com/cockroachdb/cockroach/pkg/util/tracing"
	"github.com/cockroachdb/cockroach/pkg/util/uuid"
	opentracing "github.com/opentracing/opentracing-go"
	"github.com/pkg/errors"
)

const (
	// gossipStatusInterval is the interval for logging gossip status.
	gossipStatusInterval = 1 * time.Minute

	// FirstNodeID is the node ID of the first node in a new cluster.
	FirstNodeID         = 1
	graphiteIntervalKey = "external.graphite.interval"
	maxGraphiteInterval = 15 * time.Minute
)

// Metric names.
var (
	metaExecLatency = metric.Metadata{
		Name:        "exec.latency",
		Help:        "Latency of batch KV requests executed on this node",
		Measurement: "Latency",
		Unit:        metric.Unit_NANOSECONDS,
	}
	metaExecSuccess = metric.Metadata{
		Name:        "exec.success",
		Help:        "Number of batch KV requests executed successfully on this node",
		Measurement: "Batch KV Requests",
		Unit:        metric.Unit_COUNT,
	}
	metaExecError = metric.Metadata{
		Name:        "exec.error",
		Help:        "Number of batch KV requests that failed to execute on this node",
		Measurement: "Batch KV Requests",
		Unit:        metric.Unit_COUNT,
	}
)

// Cluster settings.
var (
	// graphiteEndpoint is host:port, if any, of Graphite metrics server.
	graphiteEndpoint = settings.RegisterStringSetting(
		"external.graphite.endpoint",
		"if nonempty, push server metrics to the Graphite or Carbon server at the specified host:port",
		"",
	)
	// graphiteInterval is how often metrics are pushed to Graphite, if enabled.
	graphiteInterval = settings.RegisterValidatedDurationSetting(
		graphiteIntervalKey,
		"the interval at which metrics are pushed to Graphite (if enabled)",
		10*time.Second,
		func(v time.Duration) error {
			if v < 0 {
				return errors.Errorf("cannot set %s to a negative duration: %s", graphiteIntervalKey, v)
			} else if v > maxGraphiteInterval {
				return errors.Errorf("cannot set %s to more than %v: %s", graphiteIntervalKey, maxGraphiteInterval, v)
			}
			return nil
		},
	)
)

type nodeMetrics struct {
	Latency *metric.Histogram
	Success *metric.Counter
	Err     *metric.Counter
}

func makeNodeMetrics(reg *metric.Registry, histogramWindow time.Duration) nodeMetrics {
	nm := nodeMetrics{
		Latency: metric.NewLatency(metaExecLatency, histogramWindow),
		Success: metric.NewCounter(metaExecSuccess),
		Err:     metric.NewCounter(metaExecError),
	}
	reg.AddMetricStruct(nm)
	return nm
}

// callComplete records very high-level metrics about the number of completed
// calls and their latency. Currently, this only records statistics at the batch
// level; stats on specific lower-level kv operations are not recorded.
func (nm nodeMetrics) callComplete(d time.Duration, pErr *roachpb.Error) {
	if pErr != nil && pErr.TransactionRestart == roachpb.TransactionRestart_NONE {
		nm.Err.Inc(1)
	} else {
		nm.Success.Inc(1)
	}
	nm.Latency.RecordValue(d.Nanoseconds())
}

// A Node manages a map of stores (by store ID) for which it serves
// traffic. A node is the top-level data structure. There is one node
// instance per process. A node accepts incoming RPCs and services
// them by directing the commands contained within RPCs to local
// stores, which in turn direct the commands to specific ranges. Each
// node has access to the global, monolithic Key-Value abstraction via
// its client.DB reference. Nodes use this to allocate node and store
// IDs for bootstrapping the node itself or new stores as they're added
// on subsequent instantiations.
type Node struct {
	stopper     *stop.Stopper
	clusterID   *base.ClusterIDContainer // UUID for Cockroach cluster
	Descriptor  roachpb.NodeDescriptor   // Node ID, network/physical topology
	storeCfg    storage.StoreConfig      // Config to use and pass to stores
	eventLogger sql.EventLogger
	stores      *storage.Stores // Access to node-local stores
	metrics     nodeMetrics
	recorder    *status.MetricsRecorder
	startedAt   int64
	lastUp      int64
	initialBoot bool // True if this is the first time this node has started.
	txnMetrics  kv.TxnMetrics

	perReplicaServer storage.Server
}

// allocateNodeID increments the node id generator key to allocate
// a new, unique node id.
func allocateNodeID(ctx context.Context, db *client.DB) (roachpb.NodeID, error) {
	val, err := client.IncrementValRetryable(ctx, db, keys.NodeIDGenerator, 1)
	if err != nil {
		return 0, errors.Wrap(err, "unable to allocate node ID")
	}
	return roachpb.NodeID(val), nil
}

// allocateStoreIDs increments the store id generator key for the
// specified node to allocate "inc" new, unique store ids. The
// first ID in a contiguous range is returned on success.
func allocateStoreIDs(
	ctx context.Context, nodeID roachpb.NodeID, inc int64, db *client.DB,
) (roachpb.StoreID, error) {
	val, err := client.IncrementValRetryable(ctx, db, keys.StoreIDGenerator, inc)
	if err != nil {
		return 0, errors.Wrapf(err, "unable to allocate %d store IDs for node %d", inc, nodeID)
	}
	return roachpb.StoreID(val - inc + 1), nil
}

// GetBootstrapSchema returns the schema which will be used to bootstrap a new
// server.
func GetBootstrapSchema() sqlbase.MetadataSchema {
	return sqlbase.MakeMetadataSchema()
}

// bootstrapCluster bootstraps multiple stores using the provided engines.
// Returns the cluster ID.
//
// Ranges for various static split points are created (i.e. various system
// ranges and system tables). Note however that many of these ranges cannot be
// accessed by KV in regular means until the node liveness is written, since
// epoch-based leases cannot be granted until then.
func bootstrapCluster(
	ctx context.Context,
	cfg storage.StoreConfig,
	engines []engine.Engine,
	bootstrapVersion cluster.ClusterVersion,
	txnMetrics kv.TxnMetrics,
) (uuid.UUID, error) {
	clusterID := uuid.MakeV4()
	stopper := stop.NewStopper()
	defer stopper.Stop(ctx)

	// Make sure that the store config has a valid clock and that it doesn't
	// try to use gossip, since that can introduce race conditions.
	if cfg.Clock == nil {
		cfg.Clock = hlc.NewClock(hlc.UnixNano, time.Nanosecond)
	}
	cfg.Gossip = nil
	cfg.TestingKnobs = storage.StoreTestingKnobs{}
	cfg.ScanInterval = 10 * time.Minute
	cfg.HistogramWindowInterval = time.Duration(math.MaxInt64)
	tr := cfg.Settings.Tracer
	defer tr.Close()
	cfg.AmbientCtx.Tracer = tr
	// Create a KV DB with a sender that routes all requests to the first range
	// and first local store.
	stores := storage.NewStores(cfg.AmbientCtx, cfg.Clock, cfg.Settings.Version.MinSupportedVersion, cfg.Settings.Version.ServerVersion)
	localSender := client.Wrap(stores, func(ba roachpb.BatchRequest) roachpb.BatchRequest {
		ba.RangeID = 1
		ba.Replica.StoreID = 1
		return ba
	})
	tcsFactory := kv.NewTxnCoordSenderFactory(
		kv.TxnCoordSenderFactoryConfig{
			AmbientCtx: cfg.AmbientCtx,
			Settings:   cfg.Settings,
			Clock:      cfg.Clock,
			Stopper:    stopper,
			Metrics:    txnMetrics,
		},
		localSender,
	)

	cfg.DB = client.NewDB(cfg.AmbientCtx, tcsFactory, cfg.Clock)
	cfg.Transport = storage.NewDummyRaftTransport(cfg.Settings)
	cfg.ClosedTimestamp = container.NoopContainer()
	if err := cfg.Settings.InitializeVersion(bootstrapVersion); err != nil {
		return uuid.UUID{}, errors.Wrap(err, "while initializing cluster version")
	}
	for i, eng := range engines {
		sIdent := roachpb.StoreIdent{
			ClusterID: clusterID,
			NodeID:    FirstNodeID,
			StoreID:   roachpb.StoreID(i + 1),
		}

		// The bootstrapping store will not connect to other nodes so its
		// StoreConfig doesn't really matter.
		s := storage.NewStore(ctx, cfg, eng, &roachpb.NodeDescriptor{NodeID: FirstNodeID})

		// Bootstrap store to persist the store ident and cluster version.
		if err := storage.Bootstrap(ctx, eng, sIdent, bootstrapVersion); err != nil {
			return uuid.UUID{}, err
		}
		// Create first range, writing directly to engine. Note this does
		// not create the range, just its data. Only do this if this is the
		// first store.
		if i == 0 {
			schema := GetBootstrapSchema()
			initialValues, tableSplits := schema.GetInitialValues()
			splits := append(config.StaticSplits(), tableSplits...)
			sort.Slice(splits, func(i, j int) bool {
				return splits[i].Less(splits[j])
			})

			// The MinimumVersion is the ServerVersion when we are bootstrapping
			// a cluster (except in some tests that specifically want to set up
			// an "old-looking" cluster).
			if err := s.WriteInitialData(
				ctx, initialValues, bootstrapVersion.MinimumVersion, len(engines), splits,
			); err != nil {
				return uuid.UUID{}, err
			}
		}
		if err := s.Start(ctx, stopper); err != nil {
			return uuid.UUID{}, err
		}

		stores.AddStore(s)
	}
	return clusterID, nil
}

// duplicateBootstrapError is returned by Node.bootstrap when the node is already initialized.
type duplicateBootstrapError struct {
	ClusterID uuid.UUID
}

func (e *duplicateBootstrapError) Error() string {
	return fmt.Sprintf("cluster has already been initialized with ID %s", e.ClusterID)
}

// NewNode returns a new instance of Node.
//
// execCfg can be nil to help bootstrapping of a Server (the Node is created
// before the ExecutorConfig is initialized). In that case, InitLogger() needs
// to be called before the Node is used.
func NewNode(
	cfg storage.StoreConfig,
	recorder *status.MetricsRecorder,
	reg *metric.Registry,
	stopper *stop.Stopper,
	txnMetrics kv.TxnMetrics,
	execCfg *sql.ExecutorConfig,
	clusterID *base.ClusterIDContainer,
) *Node {
	var eventLogger sql.EventLogger
	if execCfg != nil {
		eventLogger = sql.MakeEventLogger(execCfg)
	}
	n := &Node{
		storeCfg:    cfg,
		stopper:     stopper,
		recorder:    recorder,
		metrics:     makeNodeMetrics(reg, cfg.HistogramWindowInterval),
		stores:      storage.NewStores(cfg.AmbientCtx, cfg.Clock, cfg.Settings.Version.MinSupportedVersion, cfg.Settings.Version.ServerVersion),
		txnMetrics:  txnMetrics,
		eventLogger: eventLogger,
		clusterID:   clusterID,
	}
	n.perReplicaServer = storage.MakeServer(&n.Descriptor, n.stores)
	return n
}

// InitLogger needs to be called if a nil execCfg was passed to NewNode().
func (n *Node) InitLogger(execCfg *sql.ExecutorConfig) {
	n.eventLogger = sql.MakeEventLogger(execCfg)
}

// String implements fmt.Stringer.
func (n *Node) String() string {
	return fmt.Sprintf("node=%d", n.Descriptor.NodeID)
}

// AnnotateCtx is a convenience wrapper; see AmbientContext.
func (n *Node) AnnotateCtx(ctx context.Context) context.Context {
	return n.storeCfg.AmbientCtx.AnnotateCtx(ctx)
}

// AnnotateCtxWithSpan is a convenience wrapper; see AmbientContext.
func (n *Node) AnnotateCtxWithSpan(
	ctx context.Context, opName string,
) (context.Context, opentracing.Span) {
	return n.storeCfg.AmbientCtx.AnnotateCtxWithSpan(ctx, opName)
}

func (n *Node) bootstrap(
	ctx context.Context, engines []engine.Engine, bootstrapVersion cluster.ClusterVersion,
) error {
	if n.initialBoot || n.clusterID.Get() != uuid.Nil {
		return &duplicateBootstrapError{ClusterID: n.clusterID.Get()}
	}
	n.initialBoot = true
	clusterID, err := bootstrapCluster(ctx, n.storeCfg, engines, bootstrapVersion, n.txnMetrics)
	if err != nil {
		return err
	}
	n.clusterID.Set(ctx, clusterID)

	log.Infof(ctx, "**** cluster %s has been created", clusterID)
	return nil
}

func (n *Node) onClusterVersionChange(cv cluster.ClusterVersion) {
	ctx := n.AnnotateCtx(context.Background())
	if err := n.stores.OnClusterVersionChange(ctx, cv); err != nil {
		log.Fatal(ctx, errors.Wrapf(err, "updating cluster version to %v", cv))
	}
}

// start starts the node by registering the storage instance for the
// RPC service "Node" and initializing stores for each specified
// engine. Launches periodic store gossiping in a goroutine.
// A callback can be optionally provided that will be invoked once this node's
// NodeDescriptor is available, to help bootstrapping.
func (n *Node) start(
	ctx context.Context,
	addr net.Addr,
	bootstrappedEngines, emptyEngines []engine.Engine,
	attrs roachpb.Attributes,
	locality roachpb.Locality,
	cv cluster.ClusterVersion,
	localityAddress []roachpb.LocalityAddress,
	nodeDescriptorCallback func(descriptor roachpb.NodeDescriptor),
) error {
	n.storeCfg.Settings.Version.OnChange(n.onClusterVersionChange)
	if err := n.storeCfg.Settings.InitializeVersion(cv); err != nil {
		return errors.Wrap(err, "while initializing cluster version")
	}

	// Obtaining the NodeID requires a dance of sorts. If the node has initialized
	// stores, the NodeID is persisted in each of them. If not, then we'll need to
	// use the KV store to get a NodeID assigned.
	var nodeID roachpb.NodeID
	if len(bootstrappedEngines) > 0 {
		firstIdent, err := storage.ReadStoreIdent(ctx, bootstrappedEngines[0])
		if err != nil {
			return err
		}
		nodeID = firstIdent.NodeID
	} else {
		n.initialBoot = true
		// Wait until Gossip is connected before trying to allocate a NodeID.
		// This isn't strictly necessary but avoids trying to use the KV store
		// before it can possibly work.
		if err := n.connectGossip(ctx); err != nil {
			return err
		}
		// If no NodeID has been assigned yet, allocate a new node ID.
		ctxWithSpan, span := n.AnnotateCtxWithSpan(ctx, "alloc-node-id")
		newID, err := allocateNodeID(ctxWithSpan, n.storeCfg.DB)
		if err != nil {
			return err
		}
		log.Infof(ctxWithSpan, "new node allocated ID %d", newID)
		span.Finish()
		nodeID = newID
	}

	n.startedAt = n.storeCfg.Clock.Now().WallTime
	n.Descriptor = roachpb.NodeDescriptor{
		NodeID:          nodeID,
		Address:         util.MakeUnresolvedAddr(addr.Network(), addr.String()),
		Attrs:           attrs,
		Locality:        locality,
		LocalityAddress: localityAddress,
		ServerVersion:   n.storeCfg.Settings.Version.ServerVersion,
		BuildTag:        build.GetInfo().Tag,
		StartedAt:       n.startedAt,
	}
	// Invoke any passed in nodeDescriptorCallback as soon as it's available, to
	// ensure that other components (currently the DistSQLPlanner) are initialized
	// before store startup continues.
	if nodeDescriptorCallback != nil {
		nodeDescriptorCallback(n.Descriptor)
	}

	// Gossip the node descriptor to make this node addressable by node ID.
	n.storeCfg.Gossip.NodeID.Set(ctx, n.Descriptor.NodeID)
	if err := n.storeCfg.Gossip.SetNodeDescriptor(&n.Descriptor); err != nil {
		return errors.Errorf("couldn't gossip descriptor for node %d: %s", n.Descriptor.NodeID, err)
	}

	// Start the closed timestamp subsystem.
	n.storeCfg.ClosedTimestamp.Start(n.Descriptor.NodeID)

	// Create stores from the engines that were already bootstrapped.
	for _, e := range bootstrappedEngines {
		s := storage.NewStore(ctx, n.storeCfg, e, &n.Descriptor)
		if err := s.Start(ctx, n.stopper); err != nil {
			return errors.Errorf("failed to start store: %s", err)
		}
		if s.Ident.ClusterID == (uuid.UUID{}) || s.Ident.NodeID == 0 {
			return errors.Errorf("unidentified store: %s", s)
		}
		capacity, err := s.Capacity(false /* useCached */)
		if err != nil {
			return errors.Errorf("could not query store capacity: %s", err)
		}
		log.Infof(ctx, "initialized store %s: %+v", s, capacity)

		n.addStore(s)
	}

	// Verify all initialized stores agree on cluster and node IDs.
	if err := n.validateStores(ctx); err != nil {
		return err
	}
	log.VEventf(ctx, 2, "validated stores")

	// Compute the time this node was last up; this is done by reading the
	// "last up time" from every store and choosing the most recent timestamp.
	var mostRecentTimestamp hlc.Timestamp
	if err := n.stores.VisitStores(func(s *storage.Store) error {
		timestamp, err := s.ReadLastUpTimestamp(ctx)
		if err != nil {
			return err
		}
		if mostRecentTimestamp.Less(timestamp) {
			mostRecentTimestamp = timestamp
		}
		return nil
	}); err != nil {
		return errors.Wrapf(err, "failed to read last up timestamp from stores")
	}
	n.lastUp = mostRecentTimestamp.WallTime

	// Set the stores map as the gossip persistent storage, so that
	// gossip can bootstrap using the most recently persisted set of
	// node addresses.
	if err := n.storeCfg.Gossip.SetStorage(n.stores); err != nil {
		return fmt.Errorf("failed to initialize the gossip interface: %s", err)
	}

	// Read persisted ClusterVersion from each configured store to
	// verify there are no stores with data too old or too new for this
	// binary.
	if _, err := n.stores.SynthesizeClusterVersion(ctx); err != nil {
		return err
	}

	if len(bootstrappedEngines) != 0 {
		// Connect gossip before starting bootstrap. This will be necessary
		// to bootstrap new stores. We do it before initializing the NodeID
		// as well (if needed) to avoid awkward error messages until Gossip
		// has connected.
		//
		// NB: if we have no bootstrapped engines, then we've done this above
		// already.
		if err := n.connectGossip(ctx); err != nil {
			return err
		}
	}

	// Bootstrap any uninitialized stores.
	if len(emptyEngines) > 0 {
		if err := n.bootstrapStores(ctx, emptyEngines, n.stopper); err != nil {
			return err
		}
	}

	n.startComputePeriodicMetrics(n.stopper, DefaultMetricsSampleInterval)
	// Be careful about moving this line above `startStores`; store migrations rely
	// on the fact that the cluster version has not been updated via Gossip (we
	// have migrations that want to run only if the server starts with a given
	// cluster version, but not if the server starts with a lower one and gets
	// bumped immediately, which would be possible if gossip got started earlier).
	n.startGossip(ctx, n.stopper)

	allEngines := append([]engine.Engine(nil), bootstrappedEngines...)
	allEngines = append(allEngines, emptyEngines...)
	log.Infof(ctx, "%s: started with %v engine(s) and attributes %v", n, allEngines, attrs.Attrs)
	return nil
}

// IsDraining returns true if at least one Store housed on this Node is not
// currently allowing range leases to be procured or extended.
func (n *Node) IsDraining() bool {
	var isDraining bool
	if err := n.stores.VisitStores(func(s *storage.Store) error {
		isDraining = isDraining || s.IsDraining()
		return nil
	}); err != nil {
		panic(err)
	}
	return isDraining
}

// SetDraining sets the draining mode on all of the node's underlying stores.
func (n *Node) SetDraining(drain bool) error {
	return n.stores.VisitStores(func(s *storage.Store) error {
		s.SetDraining(drain)
		return nil
	})
}

// SetHLCUpperBound sets the upper bound of the HLC wall time on all of the
// node's underlying stores.
func (n *Node) SetHLCUpperBound(ctx context.Context, hlcUpperBound int64) error {
	return n.stores.VisitStores(func(s *storage.Store) error {
		return s.WriteHLCUpperBound(ctx, hlcUpperBound)
	})
}

func (n *Node) addStore(store *storage.Store) {
	n.stores.AddStore(store)
	n.recorder.AddStore(store)
}

// validateStores iterates over all stores, verifying they agree on node ID.
// The node's ident is initialized based on the agreed-upon node ID. Note that
// cluster ID consistency is checked elsewhere in inspectEngines.
func (n *Node) validateStores(ctx context.Context) error {
	return n.stores.VisitStores(func(s *storage.Store) error {
		if n.Descriptor.NodeID != s.Ident.NodeID {
			return errors.Errorf("store %s node ID doesn't match node ID: %d", s, n.Descriptor.NodeID)
		}
		return nil
	})
}

// bootstrapStores bootstraps uninitialized stores once the cluster
// and node IDs have been established for this node. Store IDs are
// allocated via a sequence id generator stored at a system key per
// node.
func (n *Node) bootstrapStores(
	ctx context.Context, emptyEngines []engine.Engine, stopper *stop.Stopper,
) error {
	if n.clusterID.Get() == uuid.Nil {
		return errors.New("ClusterID missing during store bootstrap of auxiliary store")
	}

	// There's a bit of an awkward dance around cluster versions here. If this node
	// is joining an existing cluster for the first time, it doesn't have any engines
	// set up yet, and cv below will be the MinSupportedVersion. At the same time,
	// the Gossip update which notifies us about the real cluster version won't
	// persist it to any engines (because none of them are bootstrapped). The correct
	// version is likely in Settings.Version.Version(), but what if the callback fires
	// too late? In that case that too is the MinSupportedVersion. So we just accept
	// that we won't use the correct version here, but post-bootstrapping will invoke
	// the callback manually, which will disseminate the correct version to all engines
	// that still need it.
	cv, err := n.stores.SynthesizeClusterVersion(ctx)
	if err != nil {
		return errors.Errorf("error retrieving cluster version for bootstrap: %s", err)
	}

	{
		// Bootstrap all waiting stores by allocating a new store id for
		// each and invoking store.Bootstrap() to persist.
		inc := int64(len(emptyEngines))
		firstID, err := allocateStoreIDs(ctx, n.Descriptor.NodeID, inc, n.storeCfg.DB)
		if err != nil {
			return errors.Errorf("error allocating store ids: %s", err)
		}
		sIdent := roachpb.StoreIdent{
			ClusterID: n.clusterID.Get(),
			NodeID:    n.Descriptor.NodeID,
			StoreID:   firstID,
		}
		for _, eng := range emptyEngines {
			if err := storage.Bootstrap(ctx, eng, sIdent, cv); err != nil {
				return err
			}
			sIdent.StoreID++
		}
	}

	// Create stores from the newly bootstrapped engines.
	for _, e := range emptyEngines {
		s := storage.NewStore(ctx, n.storeCfg, e, &n.Descriptor)
		if err := s.Start(ctx, stopper); err != nil {
			return err
		}
		n.addStore(s)
		log.Infof(ctx, "bootstrapped store %s", s)
		// Done regularly in Node.startGossip, but this cuts down the time
		// until this store is used for range allocations.
		if err := s.GossipStore(ctx, false /* useCached */); err != nil {
			log.Warningf(ctx, "error doing initial gossiping: %s", err)
		}
	}

	clusterVersion := n.storeCfg.Settings.Version.Version()
	n.onClusterVersionChange(clusterVersion)

	// write a new status summary after all stores have been bootstrapped; this
	// helps the UI remain responsive when new nodes are added.
	if err := n.writeNodeStatus(ctx, 0 /* alertTTL */); err != nil {
		log.Warningf(ctx, "error writing node summary after store bootstrap: %s", err)
	}

	return nil
}

// connectGossip connects to gossip network and reads cluster ID. If
// this node is already part of a cluster, the cluster ID is verified
// for a match. If not part of a cluster, the cluster ID is set. The
// node's address is gossiped with node ID as the gossip key.
func (n *Node) connectGossip(ctx context.Context) error {
	log.Infof(ctx, "connecting to gossip network to verify cluster ID...")
	select {
	case <-n.stopper.ShouldStop():
		return errors.New("stop called before we could connect to gossip")
	case <-ctx.Done():
		return ctx.Err()
	case <-n.storeCfg.Gossip.Connected:
	}

	gossipClusterID, err := n.storeCfg.Gossip.GetClusterID()
	if err != nil {
		return err
	}
	clusterID := n.clusterID.Get()
	if clusterID == uuid.Nil {
		n.clusterID.Set(ctx, gossipClusterID)
	} else if clusterID != gossipClusterID {
		return errors.Errorf("node %d belongs to cluster %q but is attempting to connect to a gossip network for cluster %q",
			n.Descriptor.NodeID, clusterID, gossipClusterID)
	}
	log.Infof(ctx, "node connected via gossip and verified as part of cluster %q", gossipClusterID)
	return nil
}

// startGossip loops on a periodic ticker to gossip node-related
// information. Starts a goroutine to loop until the node is closed.
func (n *Node) startGossip(ctx context.Context, stopper *stop.Stopper) {
	ctx = n.AnnotateCtx(ctx)
	stopper.RunWorker(ctx, func(ctx context.Context) {
		// This should always return immediately and acts as a sanity check that we
		// don't try to gossip before we're connected.
		select {
		case <-n.storeCfg.Gossip.Connected:
		default:
			panic(fmt.Sprintf("%s: not connected to gossip", n))
		}
		// Verify we've already gossiped our node descriptor.
		if _, err := n.storeCfg.Gossip.GetNodeDescriptor(n.Descriptor.NodeID); err != nil {
			panic(err)
		}

		statusTicker := time.NewTicker(gossipStatusInterval)
		storesTicker := time.NewTicker(gossip.StoresInterval)
		nodeTicker := time.NewTicker(gossip.NodeDescriptorInterval)
		defer storesTicker.Stop()
		defer nodeTicker.Stop()
		n.gossipStores(ctx) // one-off run before going to sleep
		for {
			select {
			case <-statusTicker.C:
				n.storeCfg.Gossip.LogStatus()
			case <-storesTicker.C:
				n.gossipStores(ctx)
			case <-nodeTicker.C:
				if err := n.storeCfg.Gossip.SetNodeDescriptor(&n.Descriptor); err != nil {
					log.Warningf(ctx, "couldn't gossip descriptor for node %d: %s", n.Descriptor.NodeID, err)
				}
			case <-stopper.ShouldStop():
				return
			}
		}
	})
}

// gossipStores broadcasts each store and dead replica to the gossip network.
func (n *Node) gossipStores(ctx context.Context) {
	if err := n.stores.VisitStores(func(s *storage.Store) error {
		if err := s.GossipStore(ctx, false /* useCached */); err != nil {
			return err
		}
		return s.GossipDeadReplicas(ctx)
	}); err != nil {
		log.Warning(ctx, err)
	}
}

// startComputePeriodicMetrics starts a loop which periodically instructs each
// store to compute the value of metrics which cannot be incrementally
// maintained.
func (n *Node) startComputePeriodicMetrics(stopper *stop.Stopper, interval time.Duration) {
	ctx := n.AnnotateCtx(context.Background())
	stopper.RunWorker(ctx, func(ctx context.Context) {
		// Compute periodic stats at the same frequency as metrics are sampled.
		ticker := time.NewTicker(interval)
		defer ticker.Stop()
		for tick := 0; ; tick++ {
			select {
			case <-ticker.C:
				if err := n.computePeriodicMetrics(ctx, tick); err != nil {
					log.Errorf(ctx, "failed computing periodic metrics: %s", err)
				}
			case <-stopper.ShouldStop():
				return
			}
		}
	})
}

// computePeriodicMetrics instructs each store to compute the value of
// complicated metrics.
func (n *Node) computePeriodicMetrics(ctx context.Context, tick int) error {
	return n.stores.VisitStores(func(store *storage.Store) error {
		if err := store.ComputeMetrics(ctx, tick); err != nil {
			log.Warningf(ctx, "%s: unable to compute metrics: %s", store, err)
		}
		return nil
	})
}

func (n *Node) startGraphiteStatsExporter(st *cluster.Settings) {
	ctx := logtags.AddTag(n.AnnotateCtx(context.Background()), "graphite stats exporter", nil)
	pm := metric.MakePrometheusExporter()

	n.stopper.RunWorker(ctx, func(ctx context.Context) {
		var timer timeutil.Timer
		defer timer.Stop()
		for {
			timer.Reset(graphiteInterval.Get(&st.SV))
			select {
			case <-n.stopper.ShouldStop():
				return
			case <-timer.C:
				timer.Read = true
				endpoint := graphiteEndpoint.Get(&st.SV)
				if endpoint != "" {
					if err := n.recorder.ExportToGraphite(ctx, endpoint, &pm); err != nil {
						log.Infof(ctx, "error pushing metrics to graphite: %s\n", err)
					}
				}
			}
		}
	})
}

// startWriteNodeStatus begins periodically persisting status summaries for the
// node and its stores.
func (n *Node) startWriteNodeStatus(frequency time.Duration) {
	ctx := logtags.AddTag(n.AnnotateCtx(context.Background()), "summaries", nil)
	// Immediately record summaries once on server startup.
	n.stopper.RunWorker(ctx, func(ctx context.Context) {
		// Write a status summary immediately; this helps the UI remain
		// responsive when new nodes are added.
		if err := n.writeNodeStatus(ctx, 0 /* alertTTL */); err != nil {
			log.Warningf(ctx, "error recording initial status summaries: %s", err)
		}
		ticker := time.NewTicker(frequency)
		defer ticker.Stop()
		for {
			select {
			case <-ticker.C:
				// Use an alertTTL of twice the ticker frequency. This makes sure that
				// alerts don't disappear and reappear spuriously while at the same
				// time ensuring that an alert doesn't linger for too long after having
				// resolved.
				if err := n.writeNodeStatus(ctx, 2*frequency); err != nil {
					log.Warningf(ctx, "error recording status summaries: %s", err)
				}
			case <-n.stopper.ShouldStop():
				return
			}
		}
	})
}

// writeNodeStatus retrieves status summaries from the supplied
// NodeStatusRecorder and persists them to the cockroach data store.
func (n *Node) writeNodeStatus(ctx context.Context, alertTTL time.Duration) error {
	var err error
	if runErr := n.stopper.RunTask(ctx, "node.Node: writing summary", func(ctx context.Context) {
		nodeStatus := n.recorder.GenerateNodeStatus(ctx)
		if nodeStatus == nil {
			return
		}

		if result := n.recorder.CheckHealth(ctx, *nodeStatus); len(result.Alerts) != 0 {
			var numNodes int
			if err := n.storeCfg.Gossip.IterateInfos(gossip.KeyNodeIDPrefix, func(k string, info gossip.Info) error {
				numNodes++
				return nil
			}); err != nil {
				log.Warning(ctx, err)
			}
			if numNodes > 1 {
				// Avoid this warning on single-node clusters, which require special UX.
				log.Warningf(ctx, "health alerts detected: %+v", result)
			}
			if err := n.storeCfg.Gossip.AddInfoProto(
				gossip.MakeNodeHealthAlertKey(n.Descriptor.NodeID), &result, alertTTL,
			); err != nil {
				log.Warningf(ctx, "unable to gossip health alerts: %+v", result)
			}

			// TODO(tschottdorf): add a metric that we increment every time there are
			// alerts. This can help understand how long the cluster has been in that
			// state (since it'll be incremented every ~10s).
		}

		err = n.recorder.WriteNodeStatus(ctx, n.storeCfg.DB, *nodeStatus)
	}); runErr != nil {
		err = runErr
	}
	return err
}

// recordJoinEvent begins an asynchronous task which attempts to log a "node
// join" or "node restart" event. This query will retry until it succeeds or the
// server stops.
func (n *Node) recordJoinEvent() {
	if !n.storeCfg.LogRangeEvents {
		return
	}

	logEventType := sql.EventLogNodeRestart
	lastUp := n.lastUp
	if n.initialBoot {
		logEventType = sql.EventLogNodeJoin
		lastUp = n.startedAt
	}

	n.stopper.RunWorker(context.Background(), func(bgCtx context.Context) {
		ctx, span := n.AnnotateCtxWithSpan(bgCtx, "record-join-event")
		defer span.Finish()
		retryOpts := base.DefaultRetryOptions()
		retryOpts.Closer = n.stopper.ShouldStop()
		for r := retry.Start(retryOpts); r.Next(); {
			if err := n.storeCfg.DB.Txn(ctx, func(ctx context.Context, txn *client.Txn) error {
				return n.eventLogger.InsertEventRecord(
					ctx,
					txn,
					logEventType,
					int32(n.Descriptor.NodeID),
					int32(n.Descriptor.NodeID),
					struct {
						Descriptor roachpb.NodeDescriptor
						ClusterID  uuid.UUID
						StartedAt  int64
						LastUp     int64
					}{n.Descriptor, n.clusterID.Get(), n.startedAt, lastUp},
				)
			}); err != nil {
				log.Warningf(ctx, "%s: unable to log %s event: %s", n, logEventType, err)
			} else {
				return
			}
		}
	})
}

// If we receive a (proto-marshaled) roachpb.BatchRequest whose Requests contain
// a message type unknown to this node, we will end up with a zero entry in the
// slice. If we don't error out early, this breaks all sorts of assumptions and
// usually ends in a panic.
func checkNoUnknownRequest(reqs []roachpb.RequestUnion) *roachpb.UnsupportedRequestError {
	for _, req := range reqs {
		if req.GetValue() == nil {
			return &roachpb.UnsupportedRequestError{}
		}
	}
	return nil
}

func (n *Node) batchInternal(
	ctx context.Context, args *roachpb.BatchRequest,
) (*roachpb.BatchResponse, error) {
	if detail := checkNoUnknownRequest(args.Requests); detail != nil {
		var br roachpb.BatchResponse
		br.Error = roachpb.NewError(detail)
		return &br, nil
	}

	var br *roachpb.BatchResponse

	if err := n.stopper.RunTaskWithErr(ctx, "node.Node: batch", func(ctx context.Context) error {
		var finishSpan func(*roachpb.BatchResponse)
		// Shadow ctx from the outer function. Written like this to pass the linter.
		ctx, finishSpan = n.setupSpanForIncomingRPC(ctx, grpcutil.IsLocalRequestContext(ctx))
		defer func(br **roachpb.BatchResponse) {
			finishSpan(*br)
		}(&br)
		if log.HasSpanOrEvent(ctx) {
			log.Event(ctx, args.Summary())
		}

		tStart := timeutil.Now()
		var pErr *roachpb.Error
		br, pErr = n.stores.Send(ctx, *args)
		if pErr != nil {
			br = &roachpb.BatchResponse{}
			log.VErrEventf(ctx, 3, "%T", pErr.GetDetail())
		}
		if br.Error != nil {
			panic(roachpb.ErrorUnexpectedlySet(n.stores, br))
		}
		n.metrics.callComplete(timeutil.Since(tStart), pErr)
		br.Error = pErr
		return nil
	}); err != nil {
		return nil, err
	}
	return br, nil
}

// Batch implements the roachpb.InternalServer interface.
func (n *Node) Batch(
	ctx context.Context, args *roachpb.BatchRequest,
) (*roachpb.BatchResponse, error) {
	growStack()

	// NB: Node.Batch is called directly for "local" calls. We don't want to
	// carry the associated log tags forward as doing so makes adding additional
	// log tags more expensive and makes local calls differ from remote calls.
	ctx = n.storeCfg.AmbientCtx.ResetAndAnnotateCtx(ctx)

	br, err := n.batchInternal(ctx, args)

	// We always return errors via BatchResponse.Error so structure is
	// preserved; plain errors are presumed to be from the RPC
	// framework and not from cockroach.
	if err != nil {
		if br == nil {
			br = &roachpb.BatchResponse{}
		}
		if br.Error != nil {
			log.Fatalf(
				ctx, "attempting to return both a plain error (%s) and roachpb.Error (%s)", err, br.Error,
			)
		}
		br.Error = roachpb.NewError(err)
	}
	return br, nil
}

// setupSpanForIncomingRPC takes a context and returns a derived context with a
// new span in it. Depending on the input context, that span might be a root
// span or a child span. If it is a child span, it might be a child span of a
// local or a remote span. Note that supporting both the "child of local span"
// and "child of remote span" cases are important, as this RPC can be called
// either through the network or directly if the caller is local.
//
// It returns the derived context and a cleanup function to be called when
// servicing the RPC is done. The cleanup function will close the span and, in
// case the span was the child of a remote span and "snowball tracing" was
// enabled on that parent span, it serializes the local trace into the
// BatchResponse. The cleanup function takes the BatchResponse in which the
// response is to serialized. The BatchResponse can be nil in case no response
// is to be returned to the rpc caller.
func (n *Node) setupSpanForIncomingRPC(
	ctx context.Context, isLocalRequest bool,
) (context.Context, func(*roachpb.BatchResponse)) {
	// The operation name matches the one created by the interceptor in the
	// remoteTrace case below.
	const opName = "/cockroach.roachpb.Internal/Batch"
	var newSpan, grpcSpan opentracing.Span
	if isLocalRequest {
		// This is a local request which circumvented gRPC. Start a span now.
		ctx, newSpan = tracing.ChildSpan(ctx, opName)
	} else {
		grpcSpan = opentracing.SpanFromContext(ctx)
		if grpcSpan == nil {
			// If tracing information was passed via gRPC metadata, the gRPC interceptor
			// should have opened a span for us. If not, open a span now (if tracing is
			// disabled, this will be a noop span).
			newSpan = n.storeCfg.AmbientCtx.Tracer.(*tracing.Tracer).StartRootSpan(
				opName, n.storeCfg.AmbientCtx.LogTags(), tracing.NonRecordableSpan,
			)
			ctx = opentracing.ContextWithSpan(ctx, newSpan)
		}
	}

	finishSpan := func(br *roachpb.BatchResponse) {
		if newSpan != nil {
			newSpan.Finish()
		}
		if br == nil {
			return
		}
		if grpcSpan != nil {
			// If this is a "snowball trace", we'll need to return all the recorded
			// spans in the BatchResponse at the end of the request.
			// We don't want to do this if the operation is on the same host, in which
			// case everything is already part of the same recording.
			if rec := tracing.GetRecording(grpcSpan); rec != nil {
				br.CollectedSpans = append(br.CollectedSpans, rec...)
			}
		}
	}
	return ctx, finishSpan
}

// RangeFeed implements the roachpb.InternalServer interface.
func (n *Node) RangeFeed(
	args *roachpb.RangeFeedRequest, stream roachpb.Internal_RangeFeedServer,
) error {
	ctx := n.storeCfg.AmbientCtx.ResetAndAnnotateCtx(stream.Context())
	pErr := n.stores.RangeFeed(ctx, args, stream)
	if pErr != nil {
		var event roachpb.RangeFeedEvent
		event.SetValue(&roachpb.RangeFeedError{
			Error: *pErr,
		})
		return stream.Send(&event)
	}
	return nil
}

var growStackGlobal = false

//go:noinline
func growStack() {
	// Goroutine stacks currently start at 2 KB in size. The code paths through
	// the storage package often need a stack that is 32 KB in size. The stack
	// growth is mildly expensive making it useful to trick the runtime into
	// growing the stack early. Since goroutine stacks grow in multiples of 2 and
	// start at 2 KB in size, by placing a 16 KB object on the stack early in the
	// lifetime of a goroutine we force the runtime to use a 32 KB stack for the
	// goroutine.
	var buf [16 << 10] /* 16 KB */ byte
	if growStackGlobal {
		// Make sure the compiler doesn't optimize away buf.
		for i := range buf {
			buf[i] = byte(i)
		}
	}
}

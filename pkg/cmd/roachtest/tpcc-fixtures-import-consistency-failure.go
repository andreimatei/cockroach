package main

import (
	"context"
	"fmt"
	"time"
)

func registerTPCCFixturesImportConsistencyFailure(r *registry) {
	spec := testSpec{
		Name:    "tpcc-fixture-load-consistency-check-10000",
		Timeout: 23 * time.Hour,
		Cluster: makeClusterSpec(7, nodeCPUOption(72), nodeLifetimeOption(24*time.Hour)),
		Run: func(ctx context.Context, t *test, c *cluster) {
			runTPCCFixturesImportConsistencyFailure(ctx, t, c, 10000 /* warehouses */)
		},
	}
	r.Add(spec)
	spec = testSpec{
		Name:    "tpcc-fixture-load-consistency-check-10",
		Timeout: 24 * time.Hour,
		Cluster: makeClusterSpec(4, nodeCPUOption(8)),
		Run: func(ctx context.Context, t *test, c *cluster) {
			runTPCCFixturesImportConsistencyFailure(ctx, t, c, 10 /* warehouses */)
		},
	}
	r.Add(spec)
	// !!!
	// spec.Cluster.LocalSSD = false
	// spec.Cluster.AWSDiskSizeGB = 600
	// spec.Cluster.AWSMachineType = "c4.8xlarge"

}

func runTPCCFixturesImportConsistencyFailure(
	ctx context.Context, t *test, c *cluster, warehouses int,
) {
	c.Put(ctx, cockroach, "./cockroach", c.All())
	c.Put(ctx, workload, "./workload", c.All())
	args := startArgs(
		"--env=COCKROACH_CONSISTENCY_AGGRESSIVE=true " +
			"COCKROACH_ENGINE_MAX_SYNC_DURATION=10m " +
			"COCKROACH_LOG_MAX_SYNC_DURATION=10m")
	if err := c.StartE(ctx, c.All(), args); err != nil {
		t.Fatal(err)
	}

	m := newMonitor(ctx, c, c.All())
	m.Go(func(ctx context.Context) error {
		db, err := c.ConnE(ctx, 1)
		if err != nil {
			t.Fatal(err)
		}
		defer db.Close()
		if _, err := db.Exec(
			"set cluster setting server.consistency_check.interval = '1s'",
		); err != nil {
			t.Fatal(err)
		}

		t.l.PrintfCtx(ctx, "loading %d warehouses", warehouses)
		if err := c.RunL(ctx, t.l, c.Node(1),
			fmt.Sprintf(
				`./workload fixtures import tpcc --warehouses=%d --checks=false {pgurl:1}`,
				warehouses),
		); err != nil {
			t.l.PrintfCtx(ctx, "error importing: %s", err)
			// !!! t.Fatal(err)
		}

		var rangeID int
		var status, detail string
		t.l.Printf("Consistency check:")
		rows, err := db.Query(
			`SELECT (t.x).range_id, (t.x).status, (t.x).detail FROM
	unnest(crdb_internal.check_consistency(true, '', '')) AS t(x)`)
		if err != nil {
			// Ignore errors
			t.l.PrintfCtx(ctx, "error checking consistency: %s", err)
			return nil
		}
		defer rows.Close()
		var inconsistent bool
		for rows.Next() {
			if rows.Scan(&rangeID, &status, &detail); err != nil {
				t.Fatal(err)
			}
			t.l.Printf("%d %s %s", rangeID, status, detail)
			if status == "RANGE_INCONSISTENT" {
				inconsistent = true
			}
		}
		if inconsistent {
			t.Fatal("inconsistency found")
		}
		return nil
	})
	m.Wait()
}

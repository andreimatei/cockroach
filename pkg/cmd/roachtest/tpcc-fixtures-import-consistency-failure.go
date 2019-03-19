package main

import (
	"context"
	"time"
)

func registerTPCCFixturesImportConsistencyFailure(r *registry) {
	spec := testSpec{
		Name:    "tpcc-fixture-load-consistency-check",
		Timeout: 24 * time.Hour,
		Cluster: makeClusterSpec(7, nodeCPUOption(72)),
		Run:     testTPCCFixturesImportConsistencyFailure,
	}
	// !!!
	// spec.Cluster.LocalSSD = false
	// spec.Cluster.AWSDiskSizeGB = 600
	// spec.Cluster.AWSMachineType = "c4.8xlarge"

	r.Add(spec)
}

func testTPCCFixturesImportConsistencyFailure(ctx context.Context, t *test, c *cluster) {
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

		// !!! `./workload fixtures import tpcc --warehouses=10000 {pgurl:1}`,
		if err := c.RunL(ctx, t.l, c.Node(1),
			`./workload fixtures import tpcc --warehouses=10000 --checks=false {pgurl:1}`,
		); err != nil {
			t.Fatal(err)
		}

		var rangeID int
		var status, detail string
		t.l.Printf("Consistency check:")
		rows, err := db.Query(
			`
SELECT
	(t).*
FROM
	unnest(
		crdb_internal.check_consistency(
			true,
			e'\\x02'::BYTES,
			e'\\xff'::BYTES
		)
	)
		AS t;
	`)
		if err != nil {
			t.Fatal(err)
		}
		defer rows.Close()
		var inconsistent bool
		for rows.Next() {
			if rows.Scan(&rangeID, &status, &detail); err != nil {
				t.Fatal(err)
			}
			t.l.Printf("%d %s %s", rangeID, status, detail)
			if status != "RANGE_INDETERMINATE" {
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

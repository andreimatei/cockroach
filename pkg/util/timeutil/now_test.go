// Copyright 2017 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

package timeutil

import (
	"fmt"
	"testing"
	"time"
	_ "unsafe"
)

func BenchmarkNow(b *testing.B) {
	for i := 0; i < b.N; i++ {
		Now()
	}
}

//go:linkname cputicks runtime.cputicks
func cputicks() int64

func CPUTicks() int64

func BenchmarkCpuTicks(b *testing.B) {
	for i := 0; i < b.N; i++ {
		cputicks()
	}
}

func BenchmarkMyTicks(b *testing.B) {
	for i := 0; i < b.N; i++ {
		CPUTicks()
	}
}

func TestSizeXXX(t *testing.T) {
	t1 := CPUTicks()
	fmt.Printf("cputicks: %d\n", t1)
	for i := 0; i < 10; i++ {
		time.Sleep(time.Second)
		t2 := CPUTicks()
		fmt.Printf("after sleep: %d. delta: %d\n", t2, t2-t1)
		t1 = t2
	}
}

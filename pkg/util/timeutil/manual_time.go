// Copyright 2020 The Cockroach Authors.
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
	"container/heap"
	"container/list"
	"fmt"
	"sort"
	"time"

	"github.com/cockroachdb/cockroach/pkg/util/syncutil"
)

// ManualTime is a testing implementation of TimeSource.
type ManualTime struct {
	mu struct {
		syncutil.Mutex
		now    time.Time
		timers manualTimerQueue
		// tickers is a list with element type *manualTicker.
		tickers list.List

		// ticking, if set, indicates that the ManualTime advances with the passage
		// of real time. When ticking, `now` is not set. The timers are fired by a
		// goroutine running runTimers().
		ticking bool
		// If ticking is set, nowOffset represents the difference between the Now()
		// returned by this ManualClock, and time.Now(). This can be either positive
		// (if ManualTime.Now() is in advance of real time) or negative (if
		// ManualTime.Now() is behind real time).
		nowOffset time.Duration
	}
	// configuredForTicking !!!
	configuredForTicking bool
	// timersToggleC is used to pause and resume the timers goroutine. The channel
	// is closed when the ManualTime is shutting down and timers don't need to run
	// any more.
	timersToggleC chan struct{}
}

// NewManualTime constructs a new ManualTime.
func NewManualTime(initialTime time.Time) *ManualTime {
	mt := newManualTime()
	mt.mu.now = initialTime
	return mt
}

// NewHybridManualTime returns a ManualTime that starts intialized with
// time.Now() and is ticking.
//
// The stop function needs to be called once the ManualTime is not used anymore
// in order to stop the goroutine running the timers.
func NewHybridManualTime() (_ *ManualTime, stop func()) {
	return NewHybridManualTimeWithOpt(HybridManualTimeOpt{})
}

type HybridManualTimeOpt struct {
	// InitialTime, if non-zero, dictates the instant at which the ManualClock
	// starts.
	InitialTime time.Time

	// StartPaused, if set, causes the ManualTime to start in non-ticking mode. If
	// not set, the ManualClock starts in ticking mode. Note that it is valid for
	// StartPaused to not be set and InitialTime to be set.
	StartPaused bool
}

func NewHybridManualTimeWithOpt(opt HybridManualTimeOpt) (_ *ManualTime, stop func()) {
	m := newManualTime()
	m.configuredForTicking = true
	m.mu.ticking = true
	if !opt.InitialTime.IsZero() {
		m.mu.nowOffset = opt.InitialTime.Sub(Now())
	}
	// Start the timers goroutine. We'll pause it below if the ManualTime starts
	// as paused.
	go m.runTimers()
	if opt.StartPaused {
		m.Pause()
	}
	return m, func() {
		close(m.timersToggleC)
	}
}

func newManualTime() *ManualTime {
	m := &ManualTime{}
	m.mu.timers = manualTimerQueue{
		m: make(map[*manualTimer]int),
	}
	m.timersToggleC = make(chan struct{})
	m.mu.tickers.Init()
	return m
}

var _ TimeSource = (*ManualTime)(nil)

// !!! comment
func (m *ManualTime) StartTicking() {
	if !m.configuredForTicking {
		panic("StartTicking called on ManualTime not created with NewHybridManualTime")
	}
	m.mu.Lock()
	defer m.mu.Unlock()

	if m.mu.ticking {
		// Already ticking; nothing to do.
		return
	}

	m.mu.ticking = true
	m.mu.nowOffset = m.mu.now.Sub(Now())
	m.mu.now = time.Time{}
	// Resume the timers. The timers goroutine is currently blocked.
	m.timersToggleC <- struct{}{}
}

// !!! comment
func (m *ManualTime) Pause() {
	m.mu.Lock()
	defer m.mu.Unlock()

	if !m.mu.ticking {
		// Already in manual mode; nothing to do.
		return
	}

	// Pause the timers goroutine. We have to release the lock while synchronizing
	// with the timers goroutine.
	m.mu.Unlock()
	m.timersToggleC <- struct{}{}
	m.mu.Lock()

	m.mu.now = Now().Add(m.mu.nowOffset)
	m.mu.ticking = false
}

// Now returns the current time.
func (m *ManualTime) Now() time.Time {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.nowLocked()
}

func (m *ManualTime) nowLocked() time.Time {
	// !!! experiment with making ticking an atomic
	if m.mu.ticking {
		return Now().Add(m.mu.nowOffset)
	} else {
		return m.mu.now
	}
}

// Since implements TimeSource interface
func (m *ManualTime) Since(t time.Time) time.Duration {
	return m.Now().Sub(t)
}

// NewTimer constructs a new timer.
func (m *ManualTime) NewTimer() TimerI {
	return &manualTimer{m: m}
}

// NewTicker creates a new ticker.
func (m *ManualTime) NewTicker(duration time.Duration) TickerI {
	if duration <= 0 {
		panic("non-positive interval for NewTicker")
	}
	m.mu.Lock()
	defer m.mu.Unlock()

	t := &manualTicker{
		m:        m,
		duration: duration,
		nextTick: m.mu.now.Add(duration),
		// We allocate a big buffer so that sending a tick never blocks.
		ch: make(chan time.Time, 10000),
	}
	t.element = m.mu.tickers.PushBack(t)
	return t
}

// Advance forwards the current time by the given duration.
//
// If the timer is ticking, it will continue ticking after being advanced.
func (m *ManualTime) Advance(duration time.Duration) {
	m.AdvanceTo(m.Now().Add(duration))
}

// Backwards moves the clock back by duration. Duration is expected to be
// positive, and it will be subtracted from the current time.
//
// As opposed to the production TimeSource, timers associated with the
// ManualTime will be delayed by a backwards jump. Assuming that the ManualTime
// is in ticking mode and that a timer is scheduled to fire in one second, a
// call to Backwards(2*time.Second) will cause the timer to fire in three
// seconds (assuming no further changes to the clock). In production this
// doesn't happen because timers use the monotonic system clock.
func (m *ManualTime) Backwards(duration time.Duration) {
	if duration < 0 {
		panic("invalid negative duration")
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	// No timers fire when the clock goes backwards.
	m.mu.now = m.mu.now.Add(-duration)
}

// AdvanceTo advances the current time to t. If t is earlier than the current
// time then AdvanceTo is a no-op.
//
// If the timer is ticking, it will continue ticking after being advanced.
func (m *ManualTime) AdvanceTo(now time.Time) {
	m.advanceTo(now, false /* panicIfNotAdvancing */)
}

// MustAdvanceTo is like AdvanceTo, except it panics if now is below m's current
// time.
func (m *ManualTime) MustAdvanceTo(now time.Time) {
	m.advanceTo(now, true /* panicIfNotAdvancing */)
}

func (m *ManualTime) advanceTo(now time.Time, panicIfNotAdvancing bool) {
	// Pause the clock without holding the lock.
	if m.pauseTimersIfTicking() {
		defer m.resumeTimers()
	}

	m.mu.Lock()
	defer m.mu.Unlock()
	m.advanceToInnerLocked(now, panicIfNotAdvancing)
}

func (m *ManualTime) advanceToInnerLocked(now time.Time, panicIfNotAdvancing bool) {
	// Make sure the caller paused the clock.
	if m.mu.ticking {
		panic("expected pause clock")
	}

	oldNow := m.nowLocked()
	if !now.After(oldNow) {
		if panicIfNotAdvancing {
			panic(fmt.Sprintf("attempting to move ManualTime backwards from %s to %s", oldNow, now))
		}
		return
	}

	// Fire off any timers.
	for m.mu.timers.Len() > 0 {
		next := m.mu.timers.heap[0]
		if next.at.After(now) {
			break
		}
		next.ch <- next.at
		heap.Pop(&m.mu.timers)
	}

	// Fire off any tickers.
	for e := m.mu.tickers.Front(); e != nil; e = e.Next() {
		t := e.Value.(*manualTicker)
		for !t.nextTick.After(now) {
			select {
			case t.ch <- t.nextTick:
			default:
				panic("ticker channel full")
			}
			t.nextTick = t.nextTick.Add(t.duration)
		}
	}
}

func (m *ManualTime) addTimer(mt *manualTimer) {
	m.mu.Lock()

	if !mt.at.After(m.mu.now) {
		mt.ch <- mt.at
		m.mu.Unlock()
		return
	}
	fmt.Printf("!!! addTimer\n")
	heap.Push(&m.mu.timers, mt)
	m.mu.Unlock()
	m.notifyTimersIfTicking()
}

func (m *ManualTime) removeTimer(mt *manualTimer) bool {
	m.mu.Lock()

	if idx, ok := m.mu.timers.m[mt]; ok {
		heap.Remove(&m.mu.timers, idx)
		m.mu.Unlock()
		m.notifyTimersIfTicking()
		return true
	}
	m.mu.Unlock()
	return false
}

func (m *ManualTime) removeTicker(t *manualTicker) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if t.element != nil {
		m.mu.tickers.Remove(t.element)
		t.element = nil
	}
}

// Timers returns a snapshot of the timestamps of the pending timers.
func (m *ManualTime) Timers() []time.Time {
	m.mu.Lock()
	defer m.mu.Unlock()
	timers := make([]time.Time, m.mu.timers.Len())
	for i, t := range m.mu.timers.heap {
		timers[i] = t.at
	}
	sort.Slice(timers, func(i, j int) bool {
		return timers[i].Before(timers[j])
	})
	return timers
}

type manualTimerQueue struct {
	// m maintains the index for a timer in heap.
	m    map[*manualTimer]int
	heap []*manualTimer
}

var _ heap.Interface = (*manualTimerQueue)(nil)

func (m *manualTimerQueue) Len() int {
	return len(m.heap)
}

func (m *manualTimerQueue) Less(i, j int) bool {
	return m.heap[i].at.Before(m.heap[j].at)
}

func (m *manualTimerQueue) Swap(i, j int) {
	m.heap[i], m.heap[j] = m.heap[j], m.heap[i]
	m.m[m.heap[i]] = i
	m.m[m.heap[j]] = j
}

func (m *manualTimerQueue) Push(x interface{}) {
	mt := x.(*manualTimer)
	m.m[mt] = len(m.heap)
	m.heap = append(m.heap, mt)
}

func (m *manualTimerQueue) Pop() interface{} {
	lastIdx := len(m.heap) - 1
	ret := m.heap[lastIdx]
	delete(m.m, ret)
	m.heap = m.heap[:lastIdx]
	return ret
}

// pauseTimersIfTicking pauses the timers in case m is ticking. Returns
// true if the timers were stopped.
//
// This cannot be called concurrently with itself or resumeTimers.
func (m *ManualTime) pauseTimersIfTicking() bool {
	m.mu.Lock()
	ticking := m.mu.ticking
	m.mu.Unlock()

	if !ticking {
		// Timers are already paused.
		return false
	}

	// Pause the timers runner. We have to drop the lock before synchronizing with
	// the timers goroutine, as it might be waiting on the lock.
	m.timersToggleC <- struct{}{}
	return true
}

// resumeTimers resumes the timers runner goroutine. This should only be called
// when the runner is suspended.
func (m *ManualTime) resumeTimers() {
	// Resume the timers runner.
	m.timersToggleC <- struct{}{}
}

// notifyTimersIfTicking wakes up the timer goroutine to make sure it schedules
// the next timer. This has to be called whenever new timers are added or
// removed.
func (m *ManualTime) notifyTimersIfTicking() {
	// If the ManualTime is ticking, then pausing and resuming the timers serves
	// to force the timers goroutine to take new timers into consideration.
	if m.pauseTimersIfTicking() {
		fmt.Printf("!!! calling resume timers...\n")
		m.resumeTimers()
		fmt.Printf("!!! calling resume timers... done\n")
	}
}

// runTimers runs the timers until signaled to pause or return. Writing to the
// m.timersToggleC channel pauses and subsequently resumes the timers. The
// channel is unbuffered, so the caller can rely on the runTimers being blocked
// after the first write.
//
// When timers are resumed, runTimers looks at the heap of timers anew and waits
// for the first one. This means that a combination of pause/resume can be used
// to notify runTimers that the top of the heap might have changed.
//
// Closing m.timersToggleC signals runTimers to return.
func (m *ManualTime) runTimers() {
	// Start with a stopped timer. Note that we use time.Timer, not
	// timeutil.Timer. This allows us to reuse the Timer after calling
	// scheduledWakeup.Stop().
	scheduledWakeup := time.NewTimer(1000 * time.Hour)
	_ = scheduledWakeup.Stop()

	// We're going to run until signaled to exit the goroutine. During this time,
	// timers can be repeatedly stopped and resumed (timers stopped correspond to
	// the ManualTime being in "manual advance" mode, as opposed to the
	// "automatically ticking" mode. While stopped, we'll be blocked reading from
	// timersToggleC. While in "manual advance" mode, timers can fire unbeknownst
	// to this goroutine if the ManualTime is advanced passed a timer's
	// expiration. That's ok; if/when the goroutine is resumed, we'll refresh our
	// idea about what the first timer in line is.
	for {
		// If there are any timers, sleep until it's time for the first one to fire.
		fmt.Printf("!!! timer loop\n")
		m.mu.Lock()
		// nextC will be non-nil when scheduledWakeup is armed. It will be nil when
		// there's no timer scheduled.
		var nextC <-chan time.Time
		var nextManualTimer *manualTimer
		if len(m.mu.timers.heap) > 0 {
			nextManualTimer = m.mu.timers.heap[0]
			d := nextManualTimer.at.Sub(Now())
			fmt.Printf("!!! timer in %s\n", d)
			scheduledWakeup.Reset(nextManualTimer.at.Sub(Now()))
			nextC = scheduledWakeup.C
		} else {
			fmt.Printf("!!! timer loop: no timers\n")
			nextManualTimer, nextC = nil, nil
		}
		m.mu.Unlock()
		select {
		case <-nextC:
			fmt.Printf("!!! timer loop: maybe expired signal\n")
			m.mu.Lock()
			// Fire all expired timers.
			for m.fireFirstTimerAndPopLocked() {
			}
			m.mu.Unlock()
		case _, ok := <-m.timersToggleC:
			// We're being asked to pause the timers.

			fmt.Printf("!!! timer loop: pausing 1\n")

			// Stop and drain scheduledWakeup so that we can Reset() it on the next
			// iteration. Since we're pausing, we're no longer interested in waking up
			// at the scheduled (wall clock) time since the scheduled time no longer
			// corresponds to the ManualTime instant when the first timer fires.
			//
			// If nextC is nil, scheduledWakeup is already stopped.
			if nextC != nil && !scheduledWakeup.Stop() {
				<-nextC
			}
			fmt.Printf("!!! timer loop: pausing 2\n")
			if !ok {
				// We were signaled to exit.
				return
			}

			// Block until signaled again to resume.
			fmt.Printf("!!! timer loop: waiting for resume signal\n")
			_, ok = <-m.timersToggleC
			if !ok {
				// We were signaled to exit.
				return
			}
			fmt.Printf("!!! timer loop: resuming\n")
		}

		// !!! deal with tickers

		// Loop around and wait for the next timer.
	}
}

// fireFirstTimerAndPopLocked looks at the first timer and, if it's expired,
// signals its channel and removes it from the heap. Returns false if there are
// no timers or the first one is not yet expired.
func (m *ManualTime) fireFirstTimerAndPopLocked() bool {
	if m.mu.timers.Len() == 0 {
		return false
	}
	now := m.nowLocked()
	nextManualTimer := m.mu.timers.heap[0]
	if now.Before(nextManualTimer.at) {
		// The first timer is not yet expired.
		return false
	}
	heap.Pop(&m.mu.timers)
	nextManualTimer.ch <- now
	return true
}

type manualTimer struct {
	m  *ManualTime
	at time.Time
	ch chan time.Time
}

var _ TimerI = (*manualTimer)(nil)

func (m *manualTimer) Reset(duration time.Duration) {
	m.Stop()
	m.at = m.m.Now().Add(duration)
	m.ch = make(chan time.Time, 1)
	m.m.addTimer(m)
}

func (m *manualTimer) Stop() bool {
	removed := m.m.removeTimer(m)
	m.ch = nil
	m.at = time.Time{}
	return removed
}

func (m *manualTimer) Ch() <-chan time.Time {
	return m.ch
}

func (m *manualTimer) MarkRead() {}

type manualTicker struct {
	m       *ManualTime
	element *list.Element

	duration time.Duration
	nextTick time.Time
	ch       chan time.Time
}

// Reset is part of the TickerI interface.
func (t *manualTicker) Reset(duration time.Duration) {
	panic("not implemented")
}

// Stop is part of the TickerI interface.
func (t *manualTicker) Stop() {
	t.m.removeTicker(t)
}

// Ch is part of the TickerI interface.
func (t *manualTicker) Ch() <-chan time.Time {
	return t.ch
}

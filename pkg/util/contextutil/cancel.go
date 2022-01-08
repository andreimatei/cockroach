// Copyright 2021 The Cockroach Authors.
//
// Use of this software is governed by the Business Source License
// included in the file licenses/BSL.txt.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0, included in the file
// licenses/APL.txt.

package contextutil

import (
	"context"

	"github.com/cockroachdb/cockroach/pkg/util/syncutil"
	"github.com/cockroachdb/errors"
)

type errCancelKey struct{}

// CtxCanceledError is returned by a Context created with WithErrCancel() from
// its Err() method after it is canceled.
//
// errors.Is(CtxCanceledError, context.Canceled) returns true so that
// CtxCanceledError looks somewhat like context.Canceled.
type CtxCanceledError struct {
	inner error
}

// Error implements the error interface.
func (e CtxCanceledError) Error() string {
	return e.inner.Error()
}

// Unwrap implements the causer interface needed by the errors library.
func (e CtxCanceledError) Unwrap() error {
	return e.inner
}

// Is makes errors.Is(CtxCanceledError{}, context.Canceled) return true.
func (e CtxCanceledError) Is(other error) bool {
	return other == context.Canceled
}

// NormalFinish is a sentinel error that can be passed to the cancel() function
// returned by WithErrCancel() to signal that the cancellation is done after the
// respective operation has finished. As such, the cancel function will be
// cheaper than otherwise, as it will avoid capturing a stack trace on the
// argument that nobody is expected to be looking at this error.
var NormalFinish = CtxCanceledError{inner: errors.Wrapf(context.Canceled, "operation finished normally")}

// WithErrCancel returns a cancelable context that whose cancellation function
// takes an error. error will *not* be returned from `ctx.Err`, the
// package-level method `Err` will return the error (annotated with
// errors.WithStackDepth) for the returned context and its descendants.
func WithErrCancel(parent context.Context) (context.Context, func(error)) {
	wrappedCtx, wrappedCancel := context.WithCancel(parent)
	ctx := &errCancelCtx{
		Context: wrappedCtx,
	}
	return ctx, func(err error) {
		if err == nil {
			err = context.Canceled
		}
		if err != NormalFinish {
			err = errors.WithStackDepth(CtxCanceledError{inner: err}, 1 /* depth */)
		}
		defer wrappedCancel() // actually cancel after we've populated our ctx's inner
		ctx.mu.Lock()
		defer ctx.mu.Unlock()

		// The function has already been called.
		if ctx.err != nil {
			return
		}

		// If the parent has already been canceled, we primarily keep the parent's
		// error.
		if pErr := Err(wrappedCtx); pErr != nil {
			if err != NormalFinish {
				ctx.err = errors.WithSecondaryError(pErr, err)
			} else {
				ctx.err = pErr
			}
		} else {
			// From this moment on, ctx.Err() and Err(ctx) will return err. Similarly,
			// Err(childCtx) will also return err for every derived context that has
			// not yet been canceled, with the exception of contexts created by
			// context.WithCancel() for whom Err(childCtx) will start returning err
			// even if those contexts were already canceled (because we can't do
			// better).
			ctx.err = err
		}
	}
}

// Err returns an error associated to the Context. This is nil if the Context is
// not canceled. Otherwise, this will match `ctx.Err()` for contexts created
// with WithErrCancel. For such contexts, this is the error passed to the cancel
// function returned by WithErrCancel, or to the cancel function of one of its
// parents.
//
// For other contexts, Err returns the parentCtx.Error() on the closest parent
// created with WithErrCancel, if this context was canceled (explicitly or
// implicitly by calling one of its parents). If such a parent doesn't exist, or
// it exists but hasn't yet been been canceled, Err(ctx) returns ctx.Err().
//
// See ExampleWithErrCancel for an example.
func Err(ctx context.Context) error {
	err := ctx.Err()
	if err == nil {
		return nil
	}
	for {
		// Walk to the closest errCancelCtx parent.
		c, ok := ctx.Value(errCancelKey{}).(*errCancelCtx)
		if !ok {
			// None found, done.
			break
		}
		ctx = c.Context

		if extErr := c.getErr(); extErr != nil {
			return extErr
		}

		// Keep walking.
	}
	return err
}

type errCancelCtx struct {
	context.Context
	mu  syncutil.Mutex
	err error // protected by mu
}

func (ctx *errCancelCtx) getErr() error {
	ctx.mu.Lock()
	defer ctx.mu.Unlock()
	return ctx.err
}

func (ctx *errCancelCtx) Value(key interface{}) interface{} {
	if key == (errCancelKey{}) {
		return ctx
	}
	return ctx.Context.Value(key)
}

func (ctx *errCancelCtx) Err() error {
	ctx.mu.Lock()
	defer ctx.mu.Unlock()
	if ctx.err != nil {
		return ctx.err
	}
	return Err(ctx.Context)
}

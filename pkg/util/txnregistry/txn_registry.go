package txnregistry

import (
	"context"
	"sync"

	"github.com/cockroachdb/cockroach/pkg/util/log"
	"github.com/cockroachdb/cockroach/pkg/util/syncutil"
	"github.com/cockroachdb/cockroach/pkg/util/uuid"
)

type TxnRegistry struct {
	txns sync.Map
}

type txnEntry struct {
	mu struct {
		syncutil.Mutex

		msgs []string
	}
}

func (r *TxnRegistry) AddMsg(ctx context.Context, txnID uuid.UUID, format string, args ...interface{}) {
	msg := log.MakeMessage(ctx, format, args)
	newEntry := &txnEntry{}
	e, _ := r.txns.LoadOrStore(txnID, newEntry)
	entry := e.(*txnEntry)
	entry.mu.Lock()
	entry.mu.msgs = append(entry.mu.msgs, msg)
	entry.mu.Unlock()
}

func (r *TxnRegistry) GetMsgs(txnID uuid.UUID) []string {
	e, ok := r.txns.Load(txnID)
	if !ok {
		return nil
	}
	entry := e.(*txnEntry)
	entry.mu.Lock()
	defer entry.mu.Unlock()
	msgs := make([]string, len(entry.mu.msgs))
	copy(msgs, entry.mu.msgs)
	return msgs
}

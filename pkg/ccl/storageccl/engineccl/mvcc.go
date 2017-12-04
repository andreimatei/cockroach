// Copyright 2016 The Cockroach Authors.
//
// Licensed as a CockroachDB Enterprise file under the Cockroach Community
// License (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
//     https://github.com/cockroachdb/cockroach/blob/master/licenses/CCL.txt

package engineccl

// #cgo CPPFLAGS: -I../../../c-deps/libroach/include
// #cgo CPPFLAGS: -I../../../../c-deps/llvm/include
// #cgo LDFLAGS: -lroach
//
// // From `llvm-config --ldflags`
// #cgo LDFLAGS: -Wl,-search_paths_first -Wl,-headerpad_max_install_names
//
// // From `llvm-config --system-libs`
// #cgo LDFLAGS: -lcurses -lz -lm
//
// // Just link ... everything (definitely not necessary).
// // From `for i in $(llvm-config --libs); do echo "// #cgo LDFLAGS: $i"; done`
// #cgo LDFLAGS: -lLLVMLTO
// #cgo LDFLAGS: -lLLVMPasses
// #cgo LDFLAGS: -lLLVMObjCARCOpts
// #cgo LDFLAGS: -lLLVMSymbolize
// #cgo LDFLAGS: -lLLVMDebugInfoPDB
// #cgo LDFLAGS: -lLLVMDebugInfoDWARF
// #cgo LDFLAGS: -lLLVMMIRParser
// #cgo LDFLAGS: -lLLVMCoverage
// #cgo LDFLAGS: -lLLVMTableGen
// #cgo LDFLAGS: -lLLVMDlltoolDriver
// #cgo LDFLAGS: -lLLVMOrcJIT
// #cgo LDFLAGS: -lLLVMTestingSupport
// #cgo LDFLAGS: -lLLVMXCoreDisassembler
// #cgo LDFLAGS: -lLLVMXCoreCodeGen
// #cgo LDFLAGS: -lLLVMXCoreDesc
// #cgo LDFLAGS: -lLLVMXCoreInfo
// #cgo LDFLAGS: -lLLVMXCoreAsmPrinter
// #cgo LDFLAGS: -lLLVMSystemZDisassembler
// #cgo LDFLAGS: -lLLVMSystemZCodeGen
// #cgo LDFLAGS: -lLLVMSystemZAsmParser
// #cgo LDFLAGS: -lLLVMSystemZDesc
// #cgo LDFLAGS: -lLLVMSystemZInfo
// #cgo LDFLAGS: -lLLVMSystemZAsmPrinter
// #cgo LDFLAGS: -lLLVMSparcDisassembler
// #cgo LDFLAGS: -lLLVMSparcCodeGen
// #cgo LDFLAGS: -lLLVMSparcAsmParser
// #cgo LDFLAGS: -lLLVMSparcDesc
// #cgo LDFLAGS: -lLLVMSparcInfo
// #cgo LDFLAGS: -lLLVMSparcAsmPrinter
// #cgo LDFLAGS: -lLLVMPowerPCDisassembler
// #cgo LDFLAGS: -lLLVMPowerPCCodeGen
// #cgo LDFLAGS: -lLLVMPowerPCAsmParser
// #cgo LDFLAGS: -lLLVMPowerPCDesc
// #cgo LDFLAGS: -lLLVMPowerPCInfo
// #cgo LDFLAGS: -lLLVMPowerPCAsmPrinter
// #cgo LDFLAGS: -lLLVMNVPTXCodeGen
// #cgo LDFLAGS: -lLLVMNVPTXDesc
// #cgo LDFLAGS: -lLLVMNVPTXInfo
// #cgo LDFLAGS: -lLLVMNVPTXAsmPrinter
// #cgo LDFLAGS: -lLLVMMSP430CodeGen
// #cgo LDFLAGS: -lLLVMMSP430Desc
// #cgo LDFLAGS: -lLLVMMSP430Info
// #cgo LDFLAGS: -lLLVMMSP430AsmPrinter
// #cgo LDFLAGS: -lLLVMMipsDisassembler
// #cgo LDFLAGS: -lLLVMMipsCodeGen
// #cgo LDFLAGS: -lLLVMMipsAsmParser
// #cgo LDFLAGS: -lLLVMMipsDesc
// #cgo LDFLAGS: -lLLVMMipsInfo
// #cgo LDFLAGS: -lLLVMMipsAsmPrinter
// #cgo LDFLAGS: -lLLVMLanaiDisassembler
// #cgo LDFLAGS: -lLLVMLanaiCodeGen
// #cgo LDFLAGS: -lLLVMLanaiAsmParser
// #cgo LDFLAGS: -lLLVMLanaiDesc
// #cgo LDFLAGS: -lLLVMLanaiAsmPrinter
// #cgo LDFLAGS: -lLLVMLanaiInfo
// #cgo LDFLAGS: -lLLVMHexagonDisassembler
// #cgo LDFLAGS: -lLLVMHexagonCodeGen
// #cgo LDFLAGS: -lLLVMHexagonAsmParser
// #cgo LDFLAGS: -lLLVMHexagonDesc
// #cgo LDFLAGS: -lLLVMHexagonInfo
// #cgo LDFLAGS: -lLLVMBPFDisassembler
// #cgo LDFLAGS: -lLLVMBPFCodeGen
// #cgo LDFLAGS: -lLLVMBPFDesc
// #cgo LDFLAGS: -lLLVMBPFInfo
// #cgo LDFLAGS: -lLLVMBPFAsmPrinter
// #cgo LDFLAGS: -lLLVMARMDisassembler
// #cgo LDFLAGS: -lLLVMARMCodeGen
// #cgo LDFLAGS: -lLLVMARMAsmParser
// #cgo LDFLAGS: -lLLVMARMDesc
// #cgo LDFLAGS: -lLLVMARMInfo
// #cgo LDFLAGS: -lLLVMARMAsmPrinter
// #cgo LDFLAGS: -lLLVMAMDGPUDisassembler
// #cgo LDFLAGS: -lLLVMAMDGPUCodeGen
// #cgo LDFLAGS: -lLLVMAMDGPUAsmParser
// #cgo LDFLAGS: -lLLVMAMDGPUDesc
// #cgo LDFLAGS: -lLLVMAMDGPUInfo
// #cgo LDFLAGS: -lLLVMAMDGPUAsmPrinter
// #cgo LDFLAGS: -lLLVMAMDGPUUtils
// #cgo LDFLAGS: -lLLVMAArch64Disassembler
// #cgo LDFLAGS: -lLLVMAArch64CodeGen
// #cgo LDFLAGS: -lLLVMAArch64AsmParser
// #cgo LDFLAGS: -lLLVMAArch64Desc
// #cgo LDFLAGS: -lLLVMAArch64Info
// #cgo LDFLAGS: -lLLVMAArch64AsmPrinter
// #cgo LDFLAGS: -lLLVMAArch64Utils
// #cgo LDFLAGS: -lLLVMObjectYAML
// #cgo LDFLAGS: -lLLVMLibDriver
// #cgo LDFLAGS: -lLLVMOption
// #cgo LDFLAGS: -lgtest_main
// #cgo LDFLAGS: -lgtest
// #cgo LDFLAGS: -lLLVMX86Disassembler
// #cgo LDFLAGS: -lLLVMX86AsmParser
// #cgo LDFLAGS: -lLLVMX86CodeGen
// #cgo LDFLAGS: -lLLVMGlobalISel
// #cgo LDFLAGS: -lLLVMSelectionDAG
// #cgo LDFLAGS: -lLLVMAsmPrinter
// #cgo LDFLAGS: -lLLVMDebugInfoCodeView
// #cgo LDFLAGS: -lLLVMDebugInfoMSF
// #cgo LDFLAGS: -lLLVMX86Desc
// #cgo LDFLAGS: -lLLVMMCDisassembler
// #cgo LDFLAGS: -lLLVMX86Info
// #cgo LDFLAGS: -lLLVMX86AsmPrinter
// #cgo LDFLAGS: -lLLVMX86Utils
// #cgo LDFLAGS: -lLLVMMCJIT
// #cgo LDFLAGS: -lLLVMLineEditor
// #cgo LDFLAGS: -lLLVMInterpreter
// #cgo LDFLAGS: -lLLVMExecutionEngine
// #cgo LDFLAGS: -lLLVMRuntimeDyld
// #cgo LDFLAGS: -lLLVMCodeGen
// #cgo LDFLAGS: -lLLVMTarget
// #cgo LDFLAGS: -lLLVMCoroutines
// #cgo LDFLAGS: -lLLVMipo
// #cgo LDFLAGS: -lLLVMInstrumentation
// #cgo LDFLAGS: -lLLVMVectorize
// #cgo LDFLAGS: -lLLVMScalarOpts
// #cgo LDFLAGS: -lLLVMLinker
// #cgo LDFLAGS: -lLLVMIRReader
// #cgo LDFLAGS: -lLLVMAsmParser
// #cgo LDFLAGS: -lLLVMInstCombine
// #cgo LDFLAGS: -lLLVMTransformUtils
// #cgo LDFLAGS: -lLLVMBitWriter
// #cgo LDFLAGS: -lLLVMAnalysis
// #cgo LDFLAGS: -lLLVMProfileData
// #cgo LDFLAGS: -lLLVMObject
// #cgo LDFLAGS: -lLLVMMCParser
// #cgo LDFLAGS: -lLLVMMC
// #cgo LDFLAGS: -lLLVMBitReader
// #cgo LDFLAGS: -lLLVMCore
// #cgo LDFLAGS: -lLLVMBinaryFormat
// #cgo LDFLAGS: -lLLVMSupport
// #cgo LDFLAGS: -lLLVMDemangle
import "C"

import (
	"github.com/cockroachdb/cockroach/pkg/roachpb"
	"github.com/cockroachdb/cockroach/pkg/storage/engine"
	"github.com/cockroachdb/cockroach/pkg/storage/engine/enginepb"
	"github.com/cockroachdb/cockroach/pkg/util/hlc"
	"github.com/pkg/errors"
)

// MVCCIncrementalIterator iterates over the diff of the key range
// [startKey,endKey) and time range (startTime,endTime]. If a key was added or
// modified between startTime and endTime, the iterator will position at the
// most recent version (before or at endTime) of that key. If the key was most
// recently deleted, this is signalled with an empty value.
//
// Note: The endTime is inclusive to be consistent with the non-incremental
// iterator, where reads at a given timestamp return writes at that
// timestamp. The startTime is then made exclusive so that iterating time 1 to
// 2 and then 2 to 3 will only return values with time 2 once. An exclusive
// start time would normally make it difficult to scan timestamp 0, but
// CockroachDB uses that as a sentinel for key metadata anyway.
//
// Expected usage:
//    iter := NewMVCCIncrementalIterator(e, startTime, endTime)
//    defer iter.Close()
//    for iter.Seek(startKey); ; iter.Next() {
//        ok, err := iter.Valid()
//        if !ok { ... }
//        [code using iter.Key() and iter.Value()]
//    }
//    if err := iter.Error(); err != nil {
//      ...
//    }
type MVCCIncrementalIterator struct {
	// TODO(dan): Move all this logic into c++ and make this a thin wrapper.

	iter engine.Iterator

	startTime hlc.Timestamp
	endTime   hlc.Timestamp
	err       error
	valid     bool

	// For allocation avoidance.
	meta enginepb.MVCCMetadata
}

var _ engine.SimpleIterator = &MVCCIncrementalIterator{}

// NewMVCCIncrementalIterator creates an MVCCIncrementalIterator with the
// specified engine and time range.
func NewMVCCIncrementalIterator(
	e engine.Reader, startTime, endTime hlc.Timestamp,
) *MVCCIncrementalIterator {
	return &MVCCIncrementalIterator{
		iter:      e.NewTimeBoundIterator(startTime, endTime),
		startTime: startTime,
		endTime:   endTime,
	}
}

// Seek advances the iterator to the first key in the engine which is >= the
// provided key.
func (i *MVCCIncrementalIterator) Seek(startKey engine.MVCCKey) {
	i.iter.Seek(startKey)
	i.err = nil
	i.valid = true
	i.advance()
}

// Close frees up resources held by the iterator.
func (i *MVCCIncrementalIterator) Close() {
	i.iter.Close()
}

// Next advances the iterator to the next key/value in the iteration. After this
// call, Valid() will be true if the iterator was not positioned at the last
// key.
func (i *MVCCIncrementalIterator) Next() {
	i.iter.Next()
	i.advance()
}

// NextKey advances the iterator to the next MVCC key. This operation is
// distinct from Next which advances to the next version of the current key or
// the next key if the iterator is currently located at the last version for a
// key.
func (i *MVCCIncrementalIterator) NextKey() {
	i.iter.NextKey()
	i.advance()
}

func (i *MVCCIncrementalIterator) advance() {
	for {
		if !i.valid {
			return
		}
		if ok, err := i.iter.Valid(); !ok {
			i.err = err
			i.valid = false
			return
		}

		unsafeMetaKey := i.iter.UnsafeKey()
		if unsafeMetaKey.IsValue() {
			i.meta.Reset()
			i.meta.Timestamp = hlc.LegacyTimestamp(unsafeMetaKey.Timestamp)
		} else {
			if i.err = i.iter.ValueProto(&i.meta); i.err != nil {
				i.valid = false
				return
			}
		}
		if i.meta.IsInline() {
			// Inline values are only used in non-user data. They're not needed
			// for backup, so they're not handled by this method. If one shows
			// up, throw an error so it's obvious something is wrong.
			i.valid = false
			i.err = errors.Errorf("inline values are unsupported by MVCCIncrementalIterator: %s",
				unsafeMetaKey.Key)
			return
		}

		metaTimestamp := hlc.Timestamp(i.meta.Timestamp)
		if i.meta.Txn != nil {
			if !i.endTime.Less(metaTimestamp) {
				i.err = &roachpb.WriteIntentError{
					Intents: []roachpb.Intent{{
						Span:   roachpb.Span{Key: i.iter.Key().Key},
						Status: roachpb.PENDING,
						Txn:    *i.meta.Txn,
					}},
				}
				i.valid = false
				return
			}
			i.iter.Next()
			continue
		}

		if i.endTime.Less(metaTimestamp) {
			i.iter.Next()
			continue
		}
		if !i.startTime.Less(metaTimestamp) {
			i.iter.NextKey()
			continue
		}

		break
	}
}

// Valid must be called after any call to Reset(), Next(), or similar methods.
// It returns (true, nil) if the iterator points to a valid key (it is undefined
// to call Key(), Value(), or similar methods unless Valid() has returned (true,
// nil)). It returns (false, nil) if the iterator has moved past the end of the
// valid range, or (false, err) if an error has occurred. Valid() will never
// return true with a non-nil error.
func (i *MVCCIncrementalIterator) Valid() (bool, error) {
	return i.valid, i.err
}

// Key returns the current key.
func (i *MVCCIncrementalIterator) Key() engine.MVCCKey {
	return i.iter.Key()
}

// Value returns the current value as a byte slice.
func (i *MVCCIncrementalIterator) Value() []byte {
	return i.iter.Value()
}

// UnsafeKey returns the same key as Key, but the memory is invalidated on the
// next call to {Next,Reset,Close}.
func (i *MVCCIncrementalIterator) UnsafeKey() engine.MVCCKey {
	return i.iter.UnsafeKey()
}

// UnsafeValue returns the same value as Value, but the memory is invalidated on
// the next call to {Next,Reset,Close}.
func (i *MVCCIncrementalIterator) UnsafeValue() []byte {
	return i.iter.UnsafeValue()
}

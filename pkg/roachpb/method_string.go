// Code generated by "stringer -type=Method"; DO NOT EDIT.

package roachpb

import "fmt"

const _Method_name = "GetPutConditionalPutIncrementDeleteDeleteRangeScanScanHackReverseScanBeginTransactionEndTransactionAdminSplitAdminMergeAdminTransferLeaseAdminChangeReplicasHeartbeatTxnGCPushTxnQueryTxnRangeLookupResolveIntentResolveIntentRangeNoopMergeTruncateLogRequestLeaseTransferLeaseLeaseInfoComputeChecksumDeprecatedVerifyChecksumCheckConsistencyInitPutWriteBatchExportImportAdminScatterAddSSTable"

var _Method_index = [...]uint16{0, 3, 6, 20, 29, 35, 46, 50, 58, 69, 85, 99, 109, 119, 137, 156, 168, 170, 177, 185, 196, 209, 227, 231, 236, 247, 259, 272, 281, 296, 320, 336, 343, 353, 359, 365, 377, 387}

func (i Method) String() string {
	if i < 0 || i >= Method(len(_Method_index)-1) {
		return fmt.Sprintf("Method(%d)", i)
	}
	return _Method_name[_Method_index[i]:_Method_index[i+1]]
}

module github.com/cockroachdb/cockroach/pkg/obsservice

go 1.17

require (
	github.com/cockroachdb/cmux v0.0.0-20170110192607-30d10be49292
	github.com/cockroachdb/cockroach v20.1.17+incompatible
	github.com/cockroachdb/errors v1.9.0
	github.com/spf13/cobra v1.4.0
)

require (
	github.com/cockroachdb/logtags v0.0.0-20211118104740-dabe8e521a4f // indirect
	github.com/cockroachdb/redact v1.1.3 // indirect
	github.com/getsentry/sentry-go v0.12.0 // indirect
	github.com/gogo/protobuf v1.3.2 // indirect
	github.com/inconshreveable/mousetrap v1.0.0 // indirect
	github.com/kr/pretty v0.3.0 // indirect
	github.com/kr/text v0.2.0 // indirect
	github.com/petermattis/goid v0.0.0-20211229010228-4d14c490ee36 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	github.com/rogpeppe/go-internal v1.8.1 // indirect
	github.com/sasha-s/go-deadlock v0.3.1 // indirect
	github.com/spf13/pflag v1.0.5 // indirect
	golang.org/x/net v0.0.0-20220517181318-183a9ca12b87 // indirect
	golang.org/x/sys v0.0.0-20220422013727-9388b58f7150 // indirect
	golang.org/x/text v0.3.7 // indirect
)

replace github.com/cockroachdb/cockroach => ../..

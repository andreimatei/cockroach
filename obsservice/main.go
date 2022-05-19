package main

import (
	"crypto/tls"
	"crypto/x509"
	"encoding/pem"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"net/http"
	"net/http/httputil"
	"net/url"
	"os"
	"time"

	"github.com/cockroachdb/cmux"
	"github.com/cockroachdb/cockroach/pkg/util/syncutil"
	"github.com/cockroachdb/errors"
	"github.com/spf13/cobra"
)

// RootCmd represents the base command when called without any subcommands
var RootCmd = &cobra.Command{
	Use:   "obsservice",
	Short: "An observability service for CockroachDB",
	Long: `The Observability Service ingests monitoring and observability data 
from one or more CockroachDB clusters.`,
	Run: func(cmd *cobra.Command, args []string) {
		certs, err := loadCerts(uiCertPath, uiCertKeyPath, caCertPath)
		if err != nil {
			log.Fatal(err)
		}

		proxy := NewReverseHTTPProxy(httpAddr, crdbHttpURL, certs.CAPool, certs.UICert != nil /* canHandleTLS */)
		ch := proxy.RunAsync(certs)
		// Block forever.
		<-ch
	},
}

// Flags.
var (
	httpAddr                  string
	crdbHttpURL               string
	caCertPath                string
	uiCertPath, uiCertKeyPath string
)

func main() {
	RootCmd.PersistentFlags().StringVar(
		&httpAddr,
		"http-addr",
		"localhost:8081",
		"The address on which to listen for HTTP requests.")
	RootCmd.PersistentFlags().StringVar(
		&crdbHttpURL,
		"crdb-http-url",
		"http://localhost:8080",
		"The base URL to which HTTP requests are proxied.")
	RootCmd.PersistentFlags().StringVar(
		&caCertPath,
		"ca-cert",
		"",
		"Path to the certificate authority certificate file. If specified,"+
			" HTTP requests are only proxied to CRDB nodes that present certificates signed by this CA."+
			" If not specified, the system's CA list is used.")
	RootCmd.PersistentFlags().StringVar(
		&uiCertPath,
		"ui-cert",
		"",
		"Path to the certificate used used by the Observability Service.")
	RootCmd.PersistentFlags().StringVar(
		&uiCertKeyPath,
		"ui-cert-key",
		"",
		"Path to the private key used by the Observability Service. "+
			"This is the key corresponding to the --ui-cert certificate.")

	if err := RootCmd.Execute(); err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
}

// Certificates groups together all the certificates relevant to the proxy
// server.
type Certificates struct {
	UICertPath, UICertKeyPath string
	UICert                    *tls.Certificate
	CAPool                    *x509.CertPool
}

func loadCerts(uiCert, uiKey, caCert string) (Certificates, error) {
	var certs Certificates
	certs.UICertPath = uiCertPath
	certs.UICertKeyPath = uiKey
	if uiCert != "" {
		if uiKey == "" {
			return Certificates{}, errors.New("--ui-cert-key needs to be specified if --ui-cert is specified")
		}
		cert, err := tls.LoadX509KeyPair(uiCert, uiKey)
		if err != nil {
			return Certificates{}, errors.Wrap(err, "error parsing UI certificate")
		}
		certs.UICert = &cert
	}

	if caCert != "" {
		data, err := ioutil.ReadFile(caCert)
		if err != nil {
			return Certificates{}, errors.Wrap(err, "error reading CA cert")
		}
		block, rest := pem.Decode(data)
		if len(rest) != 0 {
			log.Fatal("More than one certificate present in %s. Not sure how to deal with that.", caCert)
		}
		cert, err := x509.ParseCertificate(block.Bytes)
		if err != nil {
			return Certificates{}, errors.Wrap(err, "error parsing CA cert")
		}
		certs.CAPool = x509.NewCertPool()
		certs.CAPool.AddCert(cert)
	}
	return certs, nil
}

type ReverseHTTPProxy struct {
	listenAddr string
	proxy      *httputil.ReverseProxy
}

// atomicURL is a thread-safe URL.
type atomicURL struct {
	mu struct {
		syncutil.Mutex // this could be a RWMutex, but it's not worth it as the critical sections are small
		url            *url.URL
	}
}

func newAtomicURL(url *url.URL) *atomicURL {
	u := &atomicURL{}
	u.mu.url = url
	return u
}

func (u *atomicURL) Get() *url.URL {
	u.mu.Lock()
	defer u.mu.Unlock()
	return u.mu.url
}

func (u *atomicURL) ReplaceScheme(newScheme string) {
	u.mu.Lock()
	defer u.mu.Unlock()
	u.mu.url.Scheme = newScheme
}

// RunAsync runs an HTTP proxy server in a goroutine. The returned channel is
// closed when the server terminates.
//
// TODO(andrei): Currently the server never terminates. Figure out a closing
// signal.
func (p *ReverseHTTPProxy) RunAsync(certs Certificates) <-chan struct{} {
	ch := make(chan struct{})

	go func() {
		defer close(ch)
		var err error

		listener, err := net.Listen("tcp", p.listenAddr)
		if err != nil {
			log.Fatal(err)
		}
		defer listener.Close()
		fmt.Printf("Listening for HTTP requests on %s.\n", p.listenAddr)

		if certs.UICert != nil {
			// We're configured to serve HTTPS. We'll also listen for HTTP requests, and redirect them
			// to HTTPS.

			// Separate HTTP traffic from HTTPS traffic.
			protocolMux := cmux.New(listener)
			clearL := protocolMux.Match(cmux.HTTP1())
			tlsL := protocolMux.Match(cmux.Any())
			// Redirect HTTP to HTTPS.
			redirectHandler := http.NewServeMux()
			redirectHandler.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
				// TODO(andrei): Consider dealing with HSTS headers. Probably drop HSTS
				// headers coming from CRDB, and set our own headers.
				http.Redirect(w, r, "https://"+r.Host+r.RequestURI, http.StatusTemporaryRedirect)
			})
			redirectServer := http.Server{Handler: redirectHandler}
			go func() {
				_ = redirectServer.Serve(clearL)
			}()

			// Serve HTTPS traffic by delegating it to the proxy.
			tlsServer := &http.Server{Handler: p.proxy}
			go func() {
				_ = tlsServer.ServeTLS(tlsL, certs.UICertPath, certs.UICertKeyPath)
			}()
			err = protocolMux.Serve()
		} else {
			// The Observability Service is not configured with certs, so it can only
			// serve HTTP.
			proxyServer := http.Server{Handler: p.proxy}
			err = proxyServer.Serve(listener)
		}
		if err != http.ErrServerClosed {
			fmt.Println(err.Error())
		}
	}()

	return ch
}

func NewReverseHTTPProxy(
	listenAddr string, crdbURL string, caCerts *x509.CertPool, canHandleTLS bool,
) ReverseHTTPProxy {
	url, err := url.Parse(crdbURL)
	if err != nil {
		log.Fatal("Invalid CRDB UI target: %s.", crdbURL)
	}
	if caCerts != nil && url.Scheme != "https" {
		log.Fatal("HTTPS is required for CRDB target when --ca-cert is specified.")
	}
	if url.Path != "" {
		// Supporting a path would require extra code in the proxy to join a
		// particular request's path with it.
		log.Fatalf("Specifying a path in --crdb-http-url is not supported.")
	}

	var httpToHttpsErr error
	if !canHandleTLS {
		httpToHttpsErr = errors.New(`CockroachDB is configured to only serve HTTPS, but the Observability Service
has not been configured for HTTPS.
Set the --ui-cert and --ui-cert-key flags to configure the Observability Service to serve HTTPS,
set the scheme in the --crdb-http-url URL to "https://", and perhaps set --ca-cert
to trust the certificate presented by CockroachDB.`)
	}

	return ReverseHTTPProxy{
		listenAddr: listenAddr,
		proxy:      newProxy(url, caCerts, httpToHttpsErr),
	}
}

// newProxy creates a proxy that can forward requests to a CRDB cluster
// identified by url. If CRDB ever returns a redirect, then the redirect target
// will be used by subsequent requests.
//
// caCerts, if not nil, specifies what CA is trusted to sign CRDB's certs. If
// nil, the system defaults are used.
//
// httpToHttpsErr, if set, will cause the proxy to detect when CRDB performs a
// HTTP to HTTPS redirection and return this error instead of proceeding to talk
// HTTPS to CRDB. The idea is that, if the Obs Service is not prepared to talk
// HTTPS to its clients, but CRDB insists on talking HTTPS to its clients, we'd
// rather return errors and ask people to configure the Obs Service for HTTPS
// than downgrade the security that CRDB insists on.
func newProxy(url *url.URL, caCerts *x509.CertPool, httpToHttpsErr error) *httputil.ReverseProxy {
	atomicTarget := newAtomicURL(url)
	director := func(req *http.Request) {
		target := atomicTarget.Get()
		req.URL.Scheme = target.Scheme
		req.URL.Host = target.Host
		targetQuery := target.RawQuery
		if targetQuery == "" || req.URL.RawQuery == "" {
			req.URL.RawQuery = targetQuery + req.URL.RawQuery
		} else {
			req.URL.RawQuery = targetQuery + "&" + req.URL.RawQuery
		}
		if _, ok := req.Header["User-Agent"]; !ok {
			// explicitly disable User-Agent so it's not set to default value
			req.Header.Set("User-Agent", "")
		}
	}
	modifyResponse := func(r *http.Response) error {
		// We deal with redirects specifically: we detect when CRDB wants us to
		// switch from HTTP to HTTPS and remember that.
		if r.StatusCode != http.StatusTemporaryRedirect &&
			r.StatusCode != http.StatusPermanentRedirect &&
			r.StatusCode != http.StatusMovedPermanently {
			return nil
		}

		// Check if CRDB is asking to switch from HTTP to HTTPS. If it is, switch
		// future requests to use HTTPS.
		redirectTarget := r.Header.Get("Location")
		newURL, err := url.Parse(redirectTarget)
		if err != nil {
			return errors.Wrap(err, "invalid redirection")
		}
		if r.Request.URL.Scheme != newURL.Scheme {
			if r.Request.URL.Scheme == "http" && newURL.Scheme == "https" {
				// If we're not prepared to server HTTPS, error out.
				if httpToHttpsErr != nil {
					return httpToHttpsErr
				}
			}
			atomicTarget.ReplaceScheme(newURL.Scheme)
			// We'll continue returning this redirect to the client. It will appear to
			// the client as a redirection to the same URL that it already requested;
			// that's fine. On the retry, we'll forward to the updated CRDB url.
		}
		return nil
	}
	proxy := &httputil.ReverseProxy{
		Director:       director,
		ModifyResponse: modifyResponse,
		// Overwrite the default error handler so that we render errors produced by
		// ModifyResponse. The default handler only logs them on the server and
		// doesn't return them to the client.
		ErrorHandler: func(rw http.ResponseWriter, req *http.Request, err error) {
			rw.WriteHeader(http.StatusInternalServerError)
			rw.Write([]byte(err.Error()))
		},
	}
	if caCerts != nil {
		// Accept only the specified roots.
		proxy.Transport = &http.Transport{
			TLSClientConfig: &tls.Config{
				RootCAs: caCerts,
			},
			TLSHandshakeTimeout: 10 * time.Second,
		}
	}
	return proxy
}

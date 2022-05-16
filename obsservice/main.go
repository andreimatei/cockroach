package main

import (
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/pem"
	"fmt"
	"io/ioutil"
	"log"
	"net/http"
	"net/http/httputil"
	"net/url"
	"os"
	"time"

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
		fmt.Printf("in root command: %s\n", crdbHTTPAddr)

		certs, err := loadCerts(uiCertPath, uiCertKeyPath, caCertPath)
		if err != nil {
			log.Fatal(err)
		}

		proxy := NewReverseHTTPProxy(crdbHTTPAddr, certs.CAPool)
		//if certs.UICert != nil {
		//	err = http.ListenAndServeTLS(httpAddr, uiCertPath, uiCertKeyPath, proxy)
		//}
		//if err != nil {
		//	log.Println("Error:", err)
		//}

		ch := proxy.RunAsync(context.Background(), certs, httpAddr)
		// !!! ReverseHttpsProxy(8082, "https://localhost:8080", "/home/andrei/cert/cert.pem", "/home/andrei/cert/key.pem")
		<-ch

	},
}

// Flags.
var (
	httpAddr                  string
	crdbHTTPAddr              string
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
		&crdbHTTPAddr,
		"crdb-http-addr",
		"http://localhost:8080",
		"The address to which HTTP requests are proxied.")
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
		block, rest := pem.Decode(data) // !!! what if there's more than one block
		log.Printf("!!! rest: %d", len(rest))
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

func (p *ReverseHTTPProxy) RunAsync(
	ctx context.Context, certs Certificates, listenAddr string,
) <-chan struct{} {
	ch := make(chan struct{})

	go func() {
		defer close(ch)
		var err error
		if certs.UICert != nil {
			go func() {
				if err := http.ListenAndServe(listenAddr, http.HandlerFunc(redirectTLS)); err != nil {
					log.Print(err)
				}
			}()

			err = http.ListenAndServeTLS(listenAddr, certs.UICertPath, certs.UICertKeyPath, p.proxy)
			// TODO(andrei): support http-to-https redirect (on the single port that we're configured with).
			// This is how it's done in CRDB:
			// https://github.com/cockroachdb/cockroach/blob/bea6834b4319c775b7823eec8ec7af53af6fafc0/pkg/server/server_http.go#L250
		} else {
			err = http.ListenAndServe(listenAddr, p.proxy)
		}
		if err != nil {
			fmt.Println(err.Error())
		}
	}()

	return ch
}

func NewReverseHTTPProxy(dst string, caCerts *x509.CertPool) ReverseHTTPProxy {
	url, err := url.Parse(dst)
	if err != nil {
		log.Fatal("invalid CRDB UI target: %s", dst)
	}
	if caCerts != nil && url.Scheme != "https" {
		log.Fatal("HTTPS is required for CRDB target")
	}

	proxy := httputil.NewSingleHostReverseProxy(url)
	if caCerts != nil {
		proxy.Transport = &http.Transport{
			// !!!
			//DialContext: (&net.Dialer{
			//	Timeout:   10 * time.Second,
			//	KeepAlive: 10 * time.Second,
			//}).DialContext,
			TLSClientConfig: &tls.Config{
				RootCAs: caCerts,
			},
			TLSHandshakeTimeout: 10 * time.Second,
		}
	}
	return ReverseHTTPProxy{
		listenAddr: "", // !!!
		proxy:      proxy,
	}
}

func redirectTLS(w http.ResponseWriter, r *http.Request) {
	http.Redirect(w, r, "https://IPAddr:443"+r.RequestURI, http.StatusMovedPermanently)
}

//func ReverseHTTPProxy(port int, dst string, cert *tls.Certificate) {
//	u, e := url.Parse(dst)
//	if e != nil {
//		log.Fatal("Bad destination.")
//	}
//	h := httputil.NewSingleHostReverseProxy(u)
//	// !!!
//	//if your certificate signed by yourself,you need use this bypass secure verify
//	var InsecureTransport http.RoundTripper = &http.Transport{
//		DialContext: (&net.Dialer{
//			Timeout:   30 * time.Second,
//			KeepAlive: 30 * time.Second,
//		}).DialContext,
//		TLSClientConfig: &tls.Config{
//			RootCAs:            nil,
//			InsecureSkipVerify: true,
//		},
//		TLSHandshakeTimeout: 10 * time.Second,
//	}
//	h.Transport = InsecureTransport
//	log.Println("listening for https")
//}

//func newReverseProxy() *httputil.ReverseProxy {
//	targetQuery := target.RawQuery
//	director := func(req *http.Request) {
//		req.URL.Scheme = target.Scheme
//		req.URL.Host = target.Host
//		req.URL.Path, req.URL.RawPath = joinURLPath(target, req.URL)
//		if targetQuery == "" || req.URL.RawQuery == "" {
//			req.URL.RawQuery = targetQuery + req.URL.RawQuery
//		} else {
//			req.URL.RawQuery = targetQuery + "&" + req.URL.RawQuery
//		}
//		if _, ok := req.Header["User-Agent"]; !ok {
//			// explicitly disable User-Agent so it's not set to default value
//			req.Header.Set("User-Agent", "")
//		}
//	}
//	return &ReverseProxy{Director: director}
//}

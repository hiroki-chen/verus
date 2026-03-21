package main

import (
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"time"
)

type reply struct {
	Path   string `json:"path"`
	Method string `json:"method"`
	Value  int    `json:"value"`
}

func main() {
	mux := http.NewServeMux()
	mux.HandleFunc("/api/data", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		_ = json.NewEncoder(w).Encode(reply{
			Path:   r.URL.Path,
			Method: r.Method,
			Value:  4242,
		})
	})

	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		panic(err)
	}
	defer ln.Close()

	server := &http.Server{
		Handler:           mux,
		ReadHeaderTimeout: 2 * time.Second,
	}
	defer server.Close()

	go func() {
		_ = server.Serve(ln)
	}()

	client := &http.Client{Timeout: 2 * time.Second}
	resp, err := client.Get("http://" + ln.Addr().String() + "/api/data")
	if err != nil {
		panic(err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		panic(fmt.Sprintf("unexpected status: %d", resp.StatusCode))
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		panic(err)
	}

	var decoded reply
	if err := json.Unmarshal(body, &decoded); err != nil {
		panic(err)
	}

	if decoded.Path != "/api/data" || decoded.Method != http.MethodGet || decoded.Value != 4242 {
		panic(fmt.Sprintf("unexpected payload: %+v", decoded))
	}

	fmt.Printf("go_http_loopback_smoke ok addr=%s bytes=%d\n", ln.Addr().String(), len(body))
}

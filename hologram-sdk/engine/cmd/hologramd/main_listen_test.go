package main

import (
	"fmt"
	"net/http"
	"os/exec"
	"strings"
	"testing"
	"time"
)

func waitHTTP(url string, d time.Duration) error {
	deadline := time.Now().Add(d)
	for time.Now().Before(deadline) {
		r, err := http.Get(url)
		if err == nil {
			r.Body.Close()
			if r.StatusCode == 200 {
				return nil
			}
		}
		time.Sleep(100 * time.Millisecond)
	}
	return fmt.Errorf("no HTTP 200 at %s within %s", url, d)
}

func TestTCPListen2375(t *testing.T) {
	cmd := exec.Command("./hologramd.exe", "--listen", "127.0.0.1:2375")
	cmd.Dir = "."
	out, _ := cmd.StdoutPipe()
	_, _ = cmd.StderrPipe()
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	defer cmd.Process.Kill()

	buf := make([]byte, 4096)
	n, _ := out.Read(buf)
	if !strings.Contains(string(buf[:n]), "Listening on: tcp://127.0.0.1:2375") {
		t.Fatalf("did not see effective endpoint, got: %s", string(buf[:n]))
	}
	if err := waitHTTP("http://127.0.0.1:2375/_ping", 3*time.Second); err != nil {
		t.Fatal(err)
	}
}

func TestHostFlagTCP(t *testing.T) {
	cmd := exec.Command("./hologramd.exe", "--host", "tcp://127.0.0.1:2376")
	cmd.Dir = "."
	out, _ := cmd.StdoutPipe()
	_, _ = cmd.StderrPipe()
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	defer cmd.Process.Kill()

	buf := make([]byte, 4096)
	n, _ := out.Read(buf)
	if !strings.Contains(string(buf[:n]), "Listening on: tcp://127.0.0.1:2376") {
		t.Fatalf("did not see effective endpoint, got: %s", string(buf[:n]))
	}
	if err := waitHTTP("http://127.0.0.1:2376/_ping", 3*time.Second); err != nil {
		t.Fatal(err)
	}
}

func TestNoZeroPortBinding(t *testing.T) {
	// This test ensures we never bind to :0
	cmd := exec.Command("./hologramd.exe", "--port", "0")
	cmd.Dir = "."
	out, _ := cmd.StdoutPipe()
	_, _ = cmd.StderrPipe()
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	defer cmd.Process.Kill()

	buf := make([]byte, 4096)
	n, _ := out.Read(buf)
	output := string(buf[:n])

	// Should either use default port or fail with clear error
	if strings.Contains(output, ":0") && !strings.Contains(output, "refusing to bind to :0") {
		t.Fatalf("daemon bound to :0 without proper error, got: %s", output)
	}
}

func TestVersionEndpoint(t *testing.T) {
	cmd := exec.Command("./hologramd.exe", "--listen", "127.0.0.1:2377")
	cmd.Dir = "."
	_, _ = cmd.StdoutPipe()
	_, _ = cmd.StderrPipe()
	if err := cmd.Start(); err != nil {
		t.Fatal(err)
	}
	defer cmd.Process.Kill()

	// Wait for startup
	time.Sleep(1 * time.Second)

	resp, err := http.Get("http://127.0.0.1:2377/version")
	if err != nil {
		t.Fatalf("version endpoint failed: %v", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		t.Fatalf("version endpoint returned %d, expected 200", resp.StatusCode)
	}

	// Check for Docker-compatible version info
	body := make([]byte, 1024)
	n, _ := resp.Body.Read(body)
	versionResp := string(body[:n])

	if !strings.Contains(versionResp, "ApiVersion") {
		t.Fatalf("version response missing ApiVersion field: %s", versionResp)
	}
}

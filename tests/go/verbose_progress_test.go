package e2e

import (
	"bufio"
	"context"
	"encoding/json"
	"io"
	"net"
	"net/http"
	"os"
	"strings"
	"testing"

	"github.com/docker/docker/api/types"
)

func TestVerboseProgressShowsXHologram(t *testing.T) {
	if os.Getenv("HOLOGRAM_VERBOSE") != "1" {
		t.Skip("run with HOLOGRAM_VERBOSE=1")
	}
	ctx := context.Background()
	cli := hgClient(t)

	// Use test knob for deterministic good witness
	// This should show XHologram progress messages in verbose mode
	reader, err := cli.ImagePull(ctx, "holo-test-ok:latest", types.ImagePullOptions{})
	if err != nil {
		t.Fatalf("image pull failed: %v", err)
	}
	defer reader.Close()

	// Read the streaming response and look for XHologram messages
	scanner := bufio.NewScanner(reader)
	foundXHologram := false

	for scanner.Scan() {
		line := scanner.Text()
		t.Logf("Progress line: %s", line)

		// Parse JSON line
		var progress map[string]interface{}
		if err := json.Unmarshal([]byte(line), &progress); err != nil {
			continue // Skip non-JSON lines
		}

		// Check for XHologram status
		if status, ok := progress["status"].(string); ok && status == "XHologram" {
			foundXHologram = true

			// Verify XHologram fields
			if uorID, ok := progress["uor_id"].(string); !ok || !strings.HasPrefix(uorID, "uor:test/ok:") {
				t.Errorf("expected uor_id with test/ok prefix, got: %v", progress["uor_id"])
			}

			if witnessOK, ok := progress["witness_ok"].(bool); !ok || !witnessOK {
				t.Errorf("expected witness_ok to be true, got: %v", progress["witness_ok"])
			}

			break
		}
	}

	if err := scanner.Err(); err != nil {
		t.Fatalf("error reading progress: %v", err)
	}

	if !foundXHologram {
		t.Fatalf("expected XHologram progress message in verbose mode")
	}
}

func TestVerboseHeaderOverride(t *testing.T) {
	// Test per-request verbose mode via header
	ctx := context.Background()

	// Make raw HTTP request with X-Hologram-Verbose header
	httpClient := &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return net.Dial("unix", "/var/run/hologramd.sock")
			},
		},
	}

	req, err := http.NewRequestWithContext(ctx, "GET", "http://unix/images/json", nil)
	if err != nil {
		t.Fatalf("create request: %v", err)
	}

	// Set verbose header
	req.Header.Set("X-Hologram-Verbose", "1")

	resp, err := httpClient.Do(req)
	if err != nil {
		t.Fatalf("HTTP request failed: %v", err)
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read response body: %v", err)
	}

	var images []map[string]interface{}
	if err := json.Unmarshal(body, &images); err != nil {
		t.Fatalf("unmarshal images: %v", err)
	}

	// Check if any image has XHologram fields (should be present due to header)
	foundXHologram := false
	for _, img := range images {
		if _, exists := img["XHologram"]; exists {
			foundXHologram = true
			break
		}
	}

	if !foundXHologram {
		t.Fatalf("expected XHologram fields with verbose header")
	}
}

func TestEnforceHeaderOverride(t *testing.T) {
	// Test per-request enforce mode via header
	ctx := context.Background()

	// Make raw HTTP request with X-Hologram-Enforce header
	httpClient := &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return net.Dial("unix", "/var/run/hologramd.sock")
			},
		},
	}

	// Try to pull a bad image with enforce header
	req, err := http.NewRequestWithContext(ctx, "POST", "http://unix/images/create?fromImage=holo-test-bad&tag=latest", nil)
	if err != nil {
		t.Fatalf("create request: %v", err)
	}

	// Set enforce header
	req.Header.Set("X-Hologram-Enforce", "1")

	resp, err := httpClient.Do(req)
	if err != nil {
		t.Fatalf("HTTP request failed: %v", err)
	}
	defer resp.Body.Close()

	// Should get an error response
	if resp.StatusCode < 400 {
		t.Fatalf("expected error response with enforce header, got status: %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("read response body: %v", err)
	}

	// Should contain witness enforcement error
	bodyStr := string(body)
	if !strings.Contains(bodyStr, "witness") && !strings.Contains(bodyStr, "enforce") {
		t.Fatalf("expected witness enforcement error, got: %s", bodyStr)
	}
}

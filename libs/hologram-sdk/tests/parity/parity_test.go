package parity

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"sort"
	"testing"
	"time"
)

// ParityTestConfig holds configuration for parity tests
type ParityTestConfig struct {
	DockerHost    string
	HologramHost  string
	GoldenDir     string
	Timeout       time.Duration
	IgnoreFields  []string
}

// DefaultParityTestConfig returns a default configuration
func DefaultParityTestConfig() *ParityTestConfig {
	return &ParityTestConfig{
		DockerHost:   "http://localhost:2375",
		HologramHost: "http://localhost:2376",
		GoldenDir:    "tests/parity/golden",
		Timeout:      30 * time.Second,
		IgnoreFields: []string{"Version", "BuildTime", "Created"},
	}
}

// ParityTest represents a single parity test
type ParityTest struct {
	Name        string
	Endpoint    string
	Method      string
	Params      map[string]string
	GoldenFile  string
	IgnoreFields []string
}

// RunParityTest runs a single parity test
func (pt *ParityTest) Run(t *testing.T, config *ParityTestConfig) {
	t.Run(pt.Name, func(t *testing.T) {
		// Get response from Docker
		dockerResp, err := pt.makeRequest(config.DockerHost, config.Timeout)
		if err != nil {
			t.Skipf("Docker daemon not available: %v", err)
			return
		}
		defer dockerResp.Body.Close()

		// Get response from Hologram
		hologramResp, err := pt.makeRequest(config.HologramHost, config.Timeout)
		if err != nil {
			t.Fatalf("Hologram daemon not available: %v", err)
		}
		defer hologramResp.Body.Close()

		// Read response bodies
		dockerBody, err := io.ReadAll(dockerResp.Body)
		if err != nil {
			t.Fatalf("Failed to read Docker response: %v", err)
		}

		hologramBody, err := io.ReadAll(hologramResp.Body)
		if err != nil {
			t.Fatalf("Failed to read Hologram response: %v", err)
		}

		// Parse JSON responses
		var dockerData, hologramData interface{}
		if err := json.Unmarshal(dockerBody, &dockerData); err != nil {
			t.Fatalf("Failed to parse Docker JSON: %v", err)
		}
		if err := json.Unmarshal(hologramBody, &hologramData); err != nil {
			t.Fatalf("Failed to parse Hologram JSON: %v", err)
		}

		// Canonicalize and compare
		dockerCanonical := pt.canonicalize(dockerData, config.IgnoreFields)
		hologramCanonical := pt.canonicalize(hologramData, config.IgnoreFields)

		if !pt.deepEqual(dockerCanonical, hologramCanonical) {
			t.Errorf("Responses differ")
			t.Errorf("Docker: %s", string(dockerBody))
			t.Errorf("Hologram: %s", string(hologramBody))
		}

		// Save golden file if it doesn't exist
		if pt.GoldenFile != "" {
			goldenPath := filepath.Join(config.GoldenDir, pt.GoldenFile)
			if _, err := os.Stat(goldenPath); os.IsNotExist(err) {
				if err := os.MkdirAll(filepath.Dir(goldenPath), 0755); err != nil {
					t.Errorf("Failed to create golden directory: %v", err)
					return
				}
				if err := os.WriteFile(goldenPath, dockerBody, 0644); err != nil {
					t.Errorf("Failed to write golden file: %v", err)
				}
			}
		}
	})
}

// makeRequest makes an HTTP request to the specified host
func (pt *ParityTest) makeRequest(host string, timeout time.Duration) (*http.Response, error) {
	client := &http.Client{Timeout: timeout}
	
	url := host + pt.Endpoint
	req, err := http.NewRequest(pt.Method, url, nil)
	if err != nil {
		return nil, err
	}

	// Add query parameters
	if pt.Params != nil {
		q := req.URL.Query()
		for k, v := range pt.Params {
			q.Add(k, v)
		}
		req.URL.RawQuery = q.Encode()
	}

	return client.Do(req)
}

// canonicalize normalizes JSON data for comparison
func (pt *ParityTest) canonicalize(data interface{}, ignoreFields []string) interface{} {
	switch v := data.(type) {
	case map[string]interface{}:
		result := make(map[string]interface{})
		for k, val := range v {
			// Skip ignored fields
			skip := false
			for _, field := range ignoreFields {
				if k == field {
					skip = true
					break
				}
			}
			if !skip {
				result[k] = pt.canonicalize(val, ignoreFields)
			}
		}
		return result
	case []interface{}:
		result := make([]interface{}, len(v))
		for i, val := range v {
			result[i] = pt.canonicalize(val, ignoreFields)
		}
		// Sort arrays for consistent comparison
		sort.Slice(result, func(i, j int) bool {
			return fmt.Sprintf("%v", result[i]) < fmt.Sprintf("%v", result[j])
		})
		return result
	default:
		return v
	}
}

// deepEqual compares two canonicalized data structures
func (pt *ParityTest) deepEqual(a, b interface{}) bool {
	switch va := a.(type) {
	case map[string]interface{}:
		vb, ok := b.(map[string]interface{})
		if !ok {
			return false
		}
		if len(va) != len(vb) {
			return false
		}
		for k, valA := range va {
			valB, exists := vb[k]
			if !exists || !pt.deepEqual(valA, valB) {
				return false
			}
		}
		return true
	case []interface{}:
		vb, ok := b.([]interface{})
		if !ok {
			return false
		}
		if len(va) != len(vb) {
			return false
		}
		for i, valA := range va {
			if !pt.deepEqual(valA, vb[i]) {
				return false
			}
		}
		return true
	default:
		return va == b
	}
}

// TestParity runs all parity tests
func TestParity(t *testing.T) {
	config := DefaultParityTestConfig()
	
	tests := []ParityTest{
		{
			Name:        "Ping",
			Endpoint:    "/_ping",
			Method:      "GET",
			GoldenFile:  "ping.txt",
		},
		{
			Name:        "Version",
			Endpoint:    "/version",
			Method:      "GET",
			GoldenFile:  "version.json",
			IgnoreFields: []string{"Version", "BuildTime", "GitCommit"},
		},
		{
			Name:        "ImagesList",
			Endpoint:    "/images/json",
			Method:      "GET",
			GoldenFile:  "images.json",
			IgnoreFields: []string{"Created"},
		},
		{
			Name:        "ImagesListWithAll",
			Endpoint:    "/images/json",
			Method:      "GET",
			Params:      map[string]string{"all": "true"},
			GoldenFile:  "images_all.json",
			IgnoreFields: []string{"Created"},
		},
	}

	for _, test := range tests {
		test.Run(t, config)
	}
}

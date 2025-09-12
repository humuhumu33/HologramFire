package api

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/hologram/engine/internal/runtime"
	"github.com/sirupsen/logrus"
)

// TestDockerParity tests that hologramd maintains Docker API compatibility
func TestDockerParity(t *testing.T) {
	// Create test runtime with minimal features
	features := runtime.HologramFeatures{
		Enabled: false, // Start with Docker-only mode
	}

	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel) // Reduce noise during tests

	rt, err := runtime.NewRuntime(context.Background(), logger, features)
	if err != nil {
		t.Fatalf("Failed to create runtime: %v", err)
	}
	defer rt.Close()

	// Create test server
	server := NewServer(logger, rt, features)

	t.Run("PingEndpoint", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/_ping", nil)
		w := httptest.NewRecorder()

		server.handlePing(w, req)

		// Check response
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		// Check content type
		contentType := w.Header().Get("Content-Type")
		if contentType != "text/plain; charset=utf-8" {
			t.Errorf("Expected content-type 'text/plain; charset=utf-8', got '%s'", contentType)
		}

		// Check body
		body := strings.TrimSpace(w.Body.String())
		if body != "OK" {
			t.Errorf("Expected body 'OK', got '%s'", body)
		}
	})

	t.Run("VersionEndpoint", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/version", nil)
		w := httptest.NewRecorder()

		server.handleVersion(w, req)

		// Check response
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		// Check content type
		contentType := w.Header().Get("Content-Type")
		if contentType != "application/json" {
			t.Errorf("Expected content-type 'application/json', got '%s'", contentType)
		}

		// Check JSON structure
		var version map[string]interface{}
		if err := json.Unmarshal(w.Body.Bytes(), &version); err != nil {
			t.Errorf("Failed to unmarshal version response: %v", err)
		}

		// Check required fields
		requiredFields := []string{"Version", "ApiVersion", "MinAPIVersion", "GitCommit", "GoVersion", "Os", "Arch"}
		for _, field := range requiredFields {
			if _, exists := version[field]; !exists {
				t.Errorf("Missing required field: %s", field)
			}
		}
	})

	t.Run("ImagesListEndpoint", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/images/json", nil)
		w := httptest.NewRecorder()

		server.ImageList(w, req)

		// Check response
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		// Check content type
		contentType := w.Header().Get("Content-Type")
		if contentType != "application/json" {
			t.Errorf("Expected content-type 'application/json', got '%s'", contentType)
		}

		// Check JSON structure
		var images []map[string]interface{}
		if err := json.Unmarshal(w.Body.Bytes(), &images); err != nil {
			t.Errorf("Failed to unmarshal images response: %v", err)
		}

		// Check that we have at least one image (hello-world)
		if len(images) == 0 {
			t.Error("Expected at least one image in response")
		}

		// Check required fields for first image
		if len(images) > 0 {
			image := images[0]
			requiredFields := []string{"Id", "RepoTags", "Created", "Size", "VirtualSize", "Labels"}
			for _, field := range requiredFields {
				if _, exists := image[field]; !exists {
					t.Errorf("Missing required field in image: %s", field)
				}
			}

			// Ensure no XHologram field in non-verbose mode
			if _, exists := image["XHologram"]; exists {
				t.Error("XHologram field should not be present in non-verbose mode")
			}
		}
	})

	t.Run("ImagesListVerboseMode", func(t *testing.T) {
		// Create server with UOR features enabled
		featuresWithUOR := runtime.HologramFeatures{
			Enabled: true,
			UORID:   true,
		}

		rtWithUOR, err := runtime.NewRuntime(context.Background(), logger, featuresWithUOR)
		if err != nil {
			t.Fatalf("Failed to create runtime with UOR: %v", err)
		}
		defer rtWithUOR.Close()

		serverWithUOR := NewServer(logger, rtWithUOR, featuresWithUOR)

		// Set verbose environment variable
		req := httptest.NewRequest("GET", "/images/json", nil)
		req.Header.Set("X-Hologram-Verbose", "true")
		w := httptest.NewRecorder()

		serverWithUOR.ImageList(w, req)

		// Check response
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		// Check JSON structure
		var images []map[string]interface{}
		if err := json.Unmarshal(w.Body.Bytes(), &images); err != nil {
			t.Errorf("Failed to unmarshal images response: %v", err)
		}

		// Check that XHologram fields are present in verbose mode
		if len(images) > 0 {
			image := images[0]
			if xHologram, exists := image["XHologram"]; exists {
				xHologramMap, ok := xHologram.(map[string]interface{})
				if !ok {
					t.Error("XHologram should be a map")
				} else {
					// Check for UOR fields
					if _, hasUORID := xHologramMap["uor_id"]; !hasUORID {
						t.Error("XHologram should contain uor_id field")
					}
					if _, hasWitnessOK := xHologramMap["witness_ok"]; !hasWitnessOK {
						t.Error("XHologram should contain witness_ok field")
					}
				}
			} else {
				t.Error("XHologram field should be present in verbose mode")
			}
		}
	})

	t.Run("ImageCreateEndpoint", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/images/create?fromImage=nginx&tag=alpine", nil)
		w := httptest.NewRecorder()

		server.ImageCreate(w, req)

		// Check response
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		// Check content type
		contentType := w.Header().Get("Content-Type")
		if contentType != "application/json" {
			t.Errorf("Expected content-type 'application/json', got '%s'", contentType)
		}

		// Check that response contains Docker-style progress events
		body := w.Body.String()
		lines := strings.Split(strings.TrimSpace(body), "\n")

		if len(lines) == 0 {
			t.Error("Expected at least one progress event")
		}

		// Check that each line is valid JSON
		for i, line := range lines {
			var event map[string]interface{}
			if err := json.Unmarshal([]byte(line), &event); err != nil {
				t.Errorf("Line %d is not valid JSON: %v", i+1, err)
			}

			// Check for required status field
			if _, exists := event["status"]; !exists {
				t.Errorf("Line %d missing 'status' field", i+1)
			}
		}
	})

	t.Run("InfoEndpoint", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/info", nil)
		w := httptest.NewRecorder()

		server.handleInfo(w, req)

		// Check response
		if w.Code != http.StatusOK {
			t.Errorf("Expected status 200, got %d", w.Code)
		}

		// Check content type
		contentType := w.Header().Get("Content-Type")
		if contentType != "application/json" {
			t.Errorf("Expected content-type 'application/json', got '%s'", contentType)
		}

		// Check JSON structure
		var info map[string]interface{}
		if err := json.Unmarshal(w.Body.Bytes(), &info); err != nil {
			t.Errorf("Failed to unmarshal info response: %v", err)
		}

		// Check required fields
		requiredFields := []string{"ID", "Containers", "Images", "Driver", "DriverStatus", "SystemStatus"}
		for _, field := range requiredFields {
			if _, exists := info[field]; !exists {
				t.Errorf("Missing required field: %s", field)
			}
		}
	})
}

// TestDockerErrorFormat tests that error responses match Docker format
func TestDockerErrorFormat(t *testing.T) {
	features := runtime.HologramFeatures{Enabled: false}
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	rt, err := runtime.NewRuntime(context.Background(), logger, features)
	if err != nil {
		t.Fatalf("Failed to create runtime: %v", err)
	}
	defer rt.Close()

	server := NewServer(logger, rt, features)

	t.Run("BadRequestError", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/images/create", nil) // Missing fromImage
		w := httptest.NewRecorder()

		server.ImageCreate(w, req)

		// Check response
		if w.Code != http.StatusBadRequest {
			t.Errorf("Expected status 400, got %d", w.Code)
		}

		// Check content type
		contentType := w.Header().Get("Content-Type")
		if contentType != "application/json" {
			t.Errorf("Expected content-type 'application/json', got '%s'", contentType)
		}

		// Check error format
		var errorResp map[string]interface{}
		if err := json.Unmarshal(w.Body.Bytes(), &errorResp); err != nil {
			t.Errorf("Failed to unmarshal error response: %v", err)
		}

		// Check for Docker-style error fields
		if _, exists := errorResp["message"]; !exists {
			t.Error("Error response missing 'message' field")
		}
	})
}

// TestStreamingResponse tests that streaming responses work correctly
func TestStreamingResponse(t *testing.T) {
	features := runtime.HologramFeatures{Enabled: false}
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	rt, err := runtime.NewRuntime(context.Background(), logger, features)
	if err != nil {
		t.Fatalf("Failed to create runtime: %v", err)
	}
	defer rt.Close()

	server := NewServer(logger, rt, features)

	t.Run("ImageCreateStreaming", func(t *testing.T) {
		req := httptest.NewRequest("POST", "/images/create?fromImage=nginx&tag=alpine", nil)
		w := httptest.NewRecorder()

		server.ImageCreate(w, req)

		// Check that response contains multiple JSON objects (one per line)
		body := w.Body.String()
		lines := strings.Split(strings.TrimSpace(body), "\n")

		if len(lines) < 3 {
			t.Errorf("Expected at least 3 progress events, got %d", len(lines))
		}

		// Verify each line is valid JSON
		for i, line := range lines {
			if strings.TrimSpace(line) == "" {
				continue
			}

			var event map[string]interface{}
			if err := json.Unmarshal([]byte(line), &event); err != nil {
				t.Errorf("Line %d is not valid JSON: %v", i+1, err)
			}
		}
	})
}

// TestHeadersCompatibility tests that headers match Docker expectations
func TestHeadersCompatibility(t *testing.T) {
	features := runtime.HologramFeatures{Enabled: false}
	logger := logrus.New()
	logger.SetLevel(logrus.ErrorLevel)

	rt, err := runtime.NewRuntime(context.Background(), logger, features)
	if err != nil {
		t.Fatalf("Failed to create runtime: %v", err)
	}
	defer rt.Close()

	server := NewServer(logger, rt, features)

	t.Run("PingHeaders", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/_ping", nil)
		w := httptest.NewRecorder()

		server.handlePing(w, req)

		// Check that ping returns text/plain; charset=utf-8
		contentType := w.Header().Get("Content-Type")
		expected := "text/plain; charset=utf-8"
		if contentType != expected {
			t.Errorf("Expected content-type '%s', got '%s'", expected, contentType)
		}
	})

	t.Run("JSONHeaders", func(t *testing.T) {
		req := httptest.NewRequest("GET", "/version", nil)
		w := httptest.NewRecorder()

		server.handleVersion(w, req)

		// Check that JSON endpoints return application/json
		contentType := w.Header().Get("Content-Type")
		expected := "application/json"
		if contentType != expected {
			t.Errorf("Expected content-type '%s', got '%s'", expected, contentType)
		}
	})
}

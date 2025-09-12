package witness

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"strings"
	"time"
)

// Verifier implements witness verification for hologram
type Verifier struct {
	config   *Config
	client   *http.Client
	endpoint string
}

// Config holds witness verifier configuration
type Config struct {
	Endpoint string
	Timeout  time.Duration
	APIKey   string
}

// NewVerifier creates a new witness verifier
func NewVerifier(config *Config) (*Verifier, error) {
	if config.Endpoint == "" {
		config.Endpoint = "http://localhost:8081"
	}
	if config.Timeout == 0 {
		config.Timeout = 10 * time.Second
	}

	client := &http.Client{
		Timeout: config.Timeout,
	}

	return &Verifier{
		config:   config,
		client:   client,
		endpoint: config.Endpoint,
	}, nil
}

// Verify verifies a witness for a UOR-ID
func (v *Verifier) Verify(ctx context.Context, uorID string) (bool, error) {
	url := fmt.Sprintf("%s/v1/witness/verify", v.endpoint)

	requestBody := map[string]string{
		"uor_id": uorID,
	}

	jsonBody, err := json.Marshal(requestBody)
	if err != nil {
		return false, fmt.Errorf("failed to marshal request: %w", err)
	}

	req, err := http.NewRequestWithContext(ctx, "POST", url, strings.NewReader(string(jsonBody)))
	if err != nil {
		return false, fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if v.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+v.config.APIKey)
	}

	req.Header.Set("Content-Type", "application/json")

	resp, err := v.client.Do(req)
	if err != nil {
		return false, fmt.Errorf("failed to verify witness: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return false, fmt.Errorf("witness verification failed: status %d", resp.StatusCode)
	}

	var result VerificationResult
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return false, fmt.Errorf("failed to decode verification result: %w", err)
	}

	return result.Valid, nil
}

// GetWitnessInfo returns witness information for a UOR-ID
func (v *Verifier) GetWitnessInfo(ctx context.Context, uorID string) (*WitnessInfo, error) {
	url := fmt.Sprintf("%s/v1/witness/%s", v.endpoint, uorID)

	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if v.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+v.config.APIKey)
	}

	resp, err := v.client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to get witness info: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("failed to get witness info: status %d", resp.StatusCode)
	}

	var witnessInfo WitnessInfo
	if err := json.NewDecoder(resp.Body).Decode(&witnessInfo); err != nil {
		return nil, fmt.Errorf("failed to decode witness info: %w", err)
	}

	return &witnessInfo, nil
}

// VerificationResult represents the result of witness verification
type VerificationResult struct {
	Valid     bool      `json:"valid"`
	Timestamp time.Time `json:"timestamp"`
	Message   string    `json:"message,omitempty"`
}

// WitnessInfo represents witness information
type WitnessInfo struct {
	UORID       string            `json:"uor_id"`
	Valid       bool              `json:"valid"`
	Timestamp   time.Time         `json:"timestamp"`
	WitnessType string            `json:"witness_type"`
	Metadata    map[string]string `json:"metadata"`
	Signature   string            `json:"signature"`
	ExpiresAt   *time.Time        `json:"expires_at,omitempty"`
}

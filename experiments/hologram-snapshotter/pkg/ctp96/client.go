package ctp96

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
	"time"
)

// Client implements CTP-96 transport protocol
type Client struct {
	config   *Config
	client   *http.Client
	endpoint string
}

// Config holds CTP-96 client configuration
type Config struct {
	Endpoint string
	Timeout  time.Duration
	APIKey   string
}

// NewClient creates a new CTP-96 client
func NewClient(config *Config) (*Client, error) {
	if config.Endpoint == "" {
		config.Endpoint = "http://localhost:8080"
	}
	if config.Timeout == 0 {
		config.Timeout = 30 * time.Second
	}

	client := &http.Client{
		Timeout: config.Timeout,
	}

	return &Client{
		config:   config,
		client:   client,
		endpoint: config.Endpoint,
	}, nil
}

// FetchManifest fetches a manifest for a UOR-ID
func (c *Client) FetchManifest(ctx context.Context, uorID string) ([]byte, error) {
	url := fmt.Sprintf("%s/v1/manifests/%s", c.endpoint, uorID)

	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if c.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+c.config.APIKey)
	}

	req.Header.Set("Accept", "application/vnd.oci.image.manifest.v1+json")

	resp, err := c.client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch manifest: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("failed to fetch manifest: status %d", resp.StatusCode)
	}

	manifest, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read manifest: %w", err)
	}

	return manifest, nil
}

// FetchContent fetches content for a digest
func (c *Client) FetchContent(ctx context.Context, uorID string, digest string) (io.ReadCloser, error) {
	url := fmt.Sprintf("%s/v1/blobs/%s", c.endpoint, digest)

	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if c.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+c.config.APIKey)
	}

	resp, err := c.client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch content: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		resp.Body.Close()
		return nil, fmt.Errorf("failed to fetch content: status %d", resp.StatusCode)
	}

	return resp.Body, nil
}

// GetSessionInfo returns session information for a UOR-ID
func (c *Client) GetSessionInfo(ctx context.Context, uorID string) (*SessionInfo, error) {
	url := fmt.Sprintf("%s/v1/sessions/%s", c.endpoint, uorID)

	req, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if c.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+c.config.APIKey)
	}

	resp, err := c.client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to get session info: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("failed to get session info: status %d", resp.StatusCode)
	}

	var sessionInfo SessionInfo
	if err := json.NewDecoder(resp.Body).Decode(&sessionInfo); err != nil {
		return nil, fmt.Errorf("failed to decode session info: %w", err)
	}

	return &sessionInfo, nil
}

// SessionInfo represents CTP-96 session information
type SessionInfo struct {
	SessionID    string            `json:"session_id"`
	UORID        string            `json:"uor_id"`
	LeaseID      string            `json:"lease_id"`
	ExpiresAt    time.Time         `json:"expires_at"`
	EnergyHints  map[string]string `json:"energy_hints"`
	LatencyHints map[string]int    `json:"latency_hints"`
}

// CreateSession creates a new CTP-96 session
func (c *Client) CreateSession(ctx context.Context, uorID string) (*SessionInfo, error) {
	url := fmt.Sprintf("%s/v1/sessions", c.endpoint)

	requestBody := map[string]string{
		"uor_id": uorID,
	}

	jsonBody, err := json.Marshal(requestBody)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	req, err := http.NewRequestWithContext(ctx, "POST", url, strings.NewReader(string(jsonBody)))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if c.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+c.config.APIKey)
	}

	req.Header.Set("Content-Type", "application/json")

	resp, err := c.client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("failed to create session: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusCreated {
		return nil, fmt.Errorf("failed to create session: status %d", resp.StatusCode)
	}

	var sessionInfo SessionInfo
	if err := json.NewDecoder(resp.Body).Decode(&sessionInfo); err != nil {
		return nil, fmt.Errorf("failed to decode session info: %w", err)
	}

	return &sessionInfo, nil
}

// CloseSession closes a CTP-96 session
func (c *Client) CloseSession(ctx context.Context, sessionID string) error {
	url := fmt.Sprintf("%s/v1/sessions/%s", c.endpoint, sessionID)

	req, err := http.NewRequestWithContext(ctx, "DELETE", url, nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	// Add authentication if API key is provided
	if c.config.APIKey != "" {
		req.Header.Set("Authorization", "Bearer "+c.config.APIKey)
	}

	resp, err := c.client.Do(req)
	if err != nil {
		return fmt.Errorf("failed to close session: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("failed to close session: status %d", resp.StatusCode)
	}

	return nil
}

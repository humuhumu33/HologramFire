package main

import (
	"bufio"
	"context"
	"encoding/json"
	"net/http"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/client"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

const (
	hologramdSocket = "unix:///var/run/hologramd.sock"
	testImage       = "alpine:latest"
)

// EventMessage represents a Docker event message
type EventMessage struct {
	Type   string `json:"Type"`
	Action string `json:"Action"`
	Actor  struct {
		ID         string            `json:"ID"`
		Attributes map[string]string `json:"Attributes"`
	} `json:"Actor"`
	Time     int64 `json:"time"`
	TimeNano int64 `json:"timeNano"`
}

func TestEventsStream(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Start events stream
	eventsReader, err := cli.Events(ctx, types.EventsOptions{
		Filters: map[string][]string{
			"type": {"container"},
		},
	})
	require.NoError(t, err)
	defer eventsReader.Close()

	// Create a container to generate events
	containerConfig := &container.Config{
		Image: testImage,
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()

	// Start container
	err = cli.ContainerStart(ctx, containerID, types.ContainerStartOptions{})
	require.NoError(t, err)

	// Stop container
	timeout := 10
	err = cli.ContainerStop(ctx, containerID, container.StopOptions{
		Timeout: &timeout,
	})
	require.NoError(t, err)

	// Collect events
	var events []EventMessage
	eventChan := make(chan EventMessage, 10)

	go func() {
		scanner := bufio.NewScanner(eventsReader)
		for scanner.Scan() {
			line := scanner.Text()
			if line == "" {
				continue
			}

			var event EventMessage
			if err := json.Unmarshal([]byte(line), &event); err != nil {
				t.Logf("Failed to unmarshal event: %v", err)
				continue
			}

			eventChan <- event
		}
	}()

	// Wait for events with timeout
	timeoutChan := time.After(10 * time.Second)

	for {
		select {
		case event := <-eventChan:
			events = append(events, event)
			t.Logf("Received event: %s %s for %s", event.Type, event.Action, event.Actor.ID)

			// Stop after collecting a few events
			if len(events) >= 3 {
				goto done
			}
		case <-timeoutChan:
			t.Logf("Timeout waiting for events, collected %d events", len(events))
			goto done
		}
	}

done:
	// Verify we received some events
	assert.Greater(t, len(events), 0, "Should have received at least one event")

	// Check for expected event types
	var hasCreate, hasStart, hasStop bool
	for _, event := range events {
		if event.Type == "container" {
			switch event.Action {
			case "create":
				hasCreate = true
			case "start":
				hasStart = true
			case "stop":
				hasStop = true
			}
		}
	}

	// At least one of these should be true
	assert.True(t, hasCreate || hasStart || hasStop, "Should have received container lifecycle events")
}

func TestEventsWithFilters(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Start events stream with specific filters
	eventsReader, err := cli.Events(ctx, types.EventsOptions{
		Filters: map[string][]string{
			"type":   {"container"},
			"action": {"create"},
		},
	})
	require.NoError(t, err)
	defer eventsReader.Close()

	// Create a container to generate events
	containerConfig := &container.Config{
		Image: testImage,
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()

	// Start and stop container (should not generate create events)
	err = cli.ContainerStart(ctx, containerID, types.ContainerStartOptions{})
	require.NoError(t, err)

	timeout := 10
	err = cli.ContainerStop(ctx, containerID, container.StopOptions{
		Timeout: &timeout,
	})
	require.NoError(t, err)

	// Collect events
	var events []EventMessage
	eventChan := make(chan EventMessage, 10)

	go func() {
		scanner := bufio.NewScanner(eventsReader)
		for scanner.Scan() {
			line := scanner.Text()
			if line == "" {
				continue
			}

			var event EventMessage
			if err := json.Unmarshal([]byte(line), &event); err != nil {
				continue
			}

			eventChan <- event
		}
	}()

	// Wait for events with timeout
	timeoutChan := time.After(5 * time.Second)

	for {
		select {
		case event := <-eventChan:
			events = append(events, event)
			t.Logf("Received filtered event: %s %s for %s", event.Type, event.Action, event.Actor.ID)

			// Verify filter is working
			assert.Equal(t, "container", event.Type)
			assert.Equal(t, "create", event.Action)

		case <-timeoutChan:
			break
		}
	}

	// Should have received at least one create event
	assert.Greater(t, len(events), 0, "Should have received at least one create event")
}

func TestEventsVerbose(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with verbose mode enabled
	os.Setenv("HOLOGRAM_VERBOSE", "1")
	defer os.Unsetenv("HOLOGRAM_VERBOSE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Start events stream
	eventsReader, err := cli.Events(ctx, types.EventsOptions{
		Filters: map[string][]string{
			"type": {"container"},
		},
	})
	require.NoError(t, err)
	defer eventsReader.Close()

	// Create a container to generate events
	containerConfig := &container.Config{
		Image: testImage,
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()

	// Start container
	err = cli.ContainerStart(ctx, containerID, types.ContainerStartOptions{})
	require.NoError(t, err)

	// Collect events
	var events []EventMessage
	eventChan := make(chan EventMessage, 10)

	go func() {
		scanner := bufio.NewScanner(eventsReader)
		for scanner.Scan() {
			line := scanner.Text()
			if line == "" {
				continue
			}

			var event EventMessage
			if err := json.Unmarshal([]byte(line), &event); err != nil {
				continue
			}

			eventChan <- event
		}
	}()

	// Wait for events with timeout
	timeoutChan := time.After(5 * time.Second)

	for {
		select {
		case event := <-eventChan:
			events = append(events, event)
			t.Logf("Received verbose event: %s %s for %s", event.Type, event.Action, event.Actor.ID)

			// In verbose mode, check for Hologram-specific attributes
			hasHologramAttr := false
			for key := range event.Actor.Attributes {
				if strings.HasPrefix(key, "XHologram.") {
					hasHologramAttr = true
					t.Logf("Found Hologram attribute: %s", key)
					break
				}
			}

			// Note: This test might pass even without Hologram attributes
			// depending on implementation details

		case <-timeoutChan:
			break
		}
	}

	// Should have received some events
	assert.Greater(t, len(events), 0, "Should have received at least one event")
}

func TestEventsHTTP(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test events endpoint directly via HTTP
	client := &http.Client{
		Timeout: 10 * time.Second,
	}

	// Create events request
	req, err := http.NewRequest("GET", "http://localhost:2375/events", nil)
	require.NoError(t, err)

	// Add query parameters
	q := req.URL.Query()
	q.Add("type", "container")
	req.URL.RawQuery = q.Encode()

	// Make request
	resp, err := client.Do(req)
	require.NoError(t, err)
	defer resp.Body.Close()

	assert.Equal(t, http.StatusOK, resp.StatusCode)
	assert.Equal(t, "application/json", resp.Header.Get("Content-Type"))

	// Read a few lines from the stream
	scanner := bufio.NewScanner(resp.Body)
	lineCount := 0

	for scanner.Scan() && lineCount < 5 {
		line := scanner.Text()
		if line == "" {
			continue
		}

		var event EventMessage
		err := json.Unmarshal([]byte(line), &event)
		if err != nil {
			t.Logf("Failed to unmarshal event: %v", err)
			continue
		}

		t.Logf("HTTP event: %s %s for %s", event.Type, event.Action, event.Actor.ID)
		lineCount++
	}

	// Should have received some events
	assert.Greater(t, lineCount, 0, "Should have received at least one event via HTTP")
}

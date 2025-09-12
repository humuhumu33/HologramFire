package main

import (
	"context"
	"io"
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

func TestContainerLifecycle(t *testing.T) {
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

	// Test container creation
	ctx := context.Background()

	// Create container
	containerConfig := &container.Config{
		Image: testImage,
		Cmd:   []string{"sh", "-c", "echo hello && sleep 1"},
	}

	hostConfig := &container.HostConfig{}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	t.Logf("Created container: %s", containerID)

	// Test container start
	err = cli.ContainerStart(ctx, containerID, types.ContainerStartOptions{})
	require.NoError(t, err)

	t.Logf("Started container: %s", containerID)

	// Wait a bit for container to run
	time.Sleep(2 * time.Second)

	// Test container inspect
	inspectResp, err := cli.ContainerInspect(ctx, containerID)
	require.NoError(t, err)

	assert.Equal(t, containerID, inspectResp.ID)
	assert.True(t, inspectResp.State.Running)
	assert.Greater(t, inspectResp.State.Pid, 0)

	t.Logf("Container state: %+v", inspectResp.State)

	// Test container logs
	logsReader, err := cli.ContainerLogs(ctx, containerID, types.ContainerLogsOptions{
		ShowStdout: true,
		ShowStderr: true,
		Timestamps: true,
	})
	require.NoError(t, err)
	defer logsReader.Close()

	logs, err := io.ReadAll(logsReader)
	require.NoError(t, err)

	logStr := string(logs)
	t.Logf("Container logs: %s", logStr)
	assert.Contains(t, logStr, "hello")

	// Test container stop
	timeout := 10
	err = cli.ContainerStop(ctx, containerID, container.StopOptions{
		Timeout: &timeout,
	})
	require.NoError(t, err)

	t.Logf("Stopped container: %s", containerID)

	// Wait for container to stop
	time.Sleep(1 * time.Second)

	// Verify container is stopped
	inspectResp, err = cli.ContainerInspect(ctx, containerID)
	require.NoError(t, err)

	assert.False(t, inspectResp.State.Running)
	assert.Equal(t, 0, inspectResp.State.ExitCode)

	// Test container removal
	err = cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{})
	require.NoError(t, err)

	t.Logf("Removed container: %s", containerID)

	// Verify container is removed
	_, err = cli.ContainerInspect(ctx, containerID)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "No such container")
}

func TestContainerCreateWithEnforce(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with enforce mode enabled
	os.Setenv("HOLOGRAM_ENFORCE", "1")
	defer os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Try to create container with "bad" image (should fail in enforce mode)
	containerConfig := &container.Config{
		Image: "holo-test-bad:latest",
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	_, err = cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "artifact witness invalid or missing")
}

func TestContainerInspectVerbose(t *testing.T) {
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

	// Create container
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

	// Inspect container
	inspectResp, err := cli.ContainerInspect(ctx, containerID)
	require.NoError(t, err)

	// Check for Hologram-specific fields in verbose mode
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the container was created successfully
	assert.Equal(t, containerID, inspectResp.ID)
	assert.Equal(t, testImage, inspectResp.Config.Image)
}

func TestContainerLogsFollow(t *testing.T) {
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

	// Create container that runs for a while
	containerConfig := &container.Config{
		Image: testImage,
		Cmd:   []string{"sh", "-c", "for i in $(seq 1 5); do echo \"Line $i\"; sleep 1; done"},
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

	// Test logs with follow
	logsReader, err := cli.ContainerLogs(ctx, containerID, types.ContainerLogsOptions{
		ShowStdout: true,
		Follow:     true,
		Timestamps: true,
	})
	require.NoError(t, err)
	defer logsReader.Close()

	// Read logs with timeout
	logChan := make(chan string, 10)
	go func() {
		buf := make([]byte, 1024)
		for {
			n, err := logsReader.Read(buf)
			if err != nil {
				break
			}
			logChan <- string(buf[:n])
		}
		close(logChan)
	}()

	// Collect logs for a few seconds
	var allLogs strings.Builder
	timeout := time.After(6 * time.Second)

	for {
		select {
		case logLine, ok := <-logChan:
			if !ok {
				goto done
			}
			allLogs.WriteString(logLine)
		case <-timeout:
			goto done
		}
	}

done:
	logStr := allLogs.String()
	t.Logf("Follow logs: %s", logStr)

	// Should contain multiple lines
	assert.Contains(t, logStr, "Line 1")
	assert.Contains(t, logStr, "Line 2")
}

func TestContainerList(t *testing.T) {
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

	// List containers (should be empty initially)
	containers, err := cli.ContainerList(ctx, types.ContainerListOptions{})
	require.NoError(t, err)

	initialCount := len(containers)
	t.Logf("Initial container count: %d", initialCount)

	// Create a container
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

	// List containers (should include the new one)
	containers, err = cli.ContainerList(ctx, types.ContainerListOptions{All: true})
	require.NoError(t, err)

	assert.GreaterOrEqual(t, len(containers), initialCount+1)

	// Find our container
	var found bool
	for _, c := range containers {
		if c.ID == containerID {
			found = true
			assert.Equal(t, testImage, c.Image)
			break
		}
	}
	assert.True(t, found, "Container should be in the list")
}

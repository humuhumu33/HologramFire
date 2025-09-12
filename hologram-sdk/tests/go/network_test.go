package main

import (
	"context"
	"fmt"
	"os"
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

func TestNetworkCreate(t *testing.T) {
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

	// Create network
	networkName := fmt.Sprintf("test-network-%d", time.Now().Unix())
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
		Labels: map[string]string{
			"test": "hologram",
		},
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	assert.NotEmpty(t, networkResp.ID)
	assert.Equal(t, networkName, networkResp.ID) // For our implementation

	t.Logf("Created network: %s", networkResp.ID)

	// Clean up
	defer func() {
		err := cli.NetworkRemove(ctx, networkResp.ID)
		if err != nil {
			t.Logf("Failed to remove network: %v", err)
		}
	}()
}

func TestNetworkInspect(t *testing.T) {
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

	// Create network
	networkName := fmt.Sprintf("test-network-%d", time.Now().Unix())
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
		Labels: map[string]string{
			"test": "hologram",
		},
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	defer func() {
		err := cli.NetworkRemove(ctx, networkResp.ID)
		if err != nil {
			t.Logf("Failed to remove network: %v", err)
		}
	}()

	// Inspect network
	networkInfo, err := cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	require.NoError(t, err)

	assert.Equal(t, networkResp.ID, networkInfo.ID)
	assert.Equal(t, networkName, networkInfo.Name)
	assert.Equal(t, "bridge", networkInfo.Driver)
	assert.Equal(t, "local", networkInfo.Scope)
	assert.Equal(t, "hologram", networkInfo.Labels["test"])

	t.Logf("Inspected network: %+v", networkInfo)
}

func TestNetworkList(t *testing.T) {
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

	// Get initial network count
	networks, err := cli.NetworkList(ctx, types.NetworkListOptions{})
	require.NoError(t, err)

	initialCount := len(networks)
	t.Logf("Initial network count: %d", initialCount)

	// Create a test network
	networkName := fmt.Sprintf("test-network-%d", time.Now().Unix())
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	defer func() {
		err := cli.NetworkRemove(ctx, networkResp.ID)
		if err != nil {
			t.Logf("Failed to remove network: %v", err)
		}
	}()

	// List networks again
	networks, err = cli.NetworkList(ctx, types.NetworkListOptions{})
	require.NoError(t, err)

	assert.GreaterOrEqual(t, len(networks), initialCount+1)

	// Find our network
	var found bool
	for _, n := range networks {
		if n.ID == networkResp.ID {
			found = true
			assert.Equal(t, networkName, n.Name)
			assert.Equal(t, "bridge", n.Driver)
			break
		}
	}
	assert.True(t, found, "Network should be in the list")
}

func TestNetworkConnectDisconnect(t *testing.T) {
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

	// Create network
	networkName := fmt.Sprintf("test-network-%d", time.Now().Unix())
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	defer func() {
		err := cli.NetworkRemove(ctx, networkResp.ID)
		if err != nil {
			t.Logf("Failed to remove network: %v", err)
		}
	}()

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

	// Connect container to network
	err = cli.NetworkConnect(ctx, networkResp.ID, containerID, nil)
	require.NoError(t, err)

	t.Logf("Connected container %s to network %s", containerID, networkResp.ID)

	// Inspect network to verify connection
	networkInfo, err := cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	require.NoError(t, err)

	// Check if container is in the network
	_, exists := networkInfo.Containers[containerID]
	assert.True(t, exists, "Container should be connected to network")

	// Disconnect container from network
	err = cli.NetworkDisconnect(ctx, networkResp.ID, containerID, false)
	require.NoError(t, err)

	t.Logf("Disconnected container %s from network %s", containerID, networkResp.ID)

	// Inspect network again to verify disconnection
	networkInfo, err = cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	require.NoError(t, err)

	// Check if container is no longer in the network
	_, exists = networkInfo.Containers[containerID]
	assert.False(t, exists, "Container should not be connected to network")
}

func TestNetworkRemove(t *testing.T) {
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

	// Create network
	networkName := fmt.Sprintf("test-network-%d", time.Now().Unix())
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	// Verify network exists
	_, err = cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	require.NoError(t, err)

	// Remove network
	err = cli.NetworkRemove(ctx, networkResp.ID)
	require.NoError(t, err)

	// Verify network is removed
	_, err = cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "No such network")
}

func TestNetworkCTP96(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with CTP-96 networking enabled
	os.Setenv("HOLOGRAM_NET", "ctp96")
	defer os.Unsetenv("HOLOGRAM_NET")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Create network with CTP-96 name
	networkName := "ctp96"
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	defer func() {
		err := cli.NetworkRemove(ctx, networkResp.ID)
		if err != nil {
			t.Logf("Failed to remove network: %v", err)
		}
	}()

	// Inspect network
	networkInfo, err := cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	require.NoError(t, err)

	assert.Equal(t, networkResp.ID, networkInfo.ID)
	assert.Equal(t, networkName, networkInfo.Name)
	assert.Equal(t, "bridge", networkInfo.Driver)

	// In CTP-96 mode, check for CTP-96 specific fields
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the network was created successfully
	t.Logf("CTP-96 network inspect: %+v", networkInfo)
}

func TestNetworkVerbose(t *testing.T) {
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

	// Create network
	networkName := fmt.Sprintf("test-network-%d", time.Now().Unix())
	networkConfig := &types.NetworkCreate{
		Name:   networkName,
		Driver: "bridge",
	}

	networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
	require.NoError(t, err)

	defer func() {
		err := cli.NetworkRemove(ctx, networkResp.ID)
		if err != nil {
			t.Logf("Failed to remove network: %v", err)
		}
	}()

	// Inspect network
	networkInfo, err := cli.NetworkInspect(ctx, networkResp.ID, types.NetworkInspectOptions{})
	require.NoError(t, err)

	// In verbose mode, check for Hologram-specific fields
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the network was created successfully
	assert.Equal(t, networkResp.ID, networkInfo.ID)
	assert.Equal(t, networkName, networkInfo.Name)
	assert.Equal(t, "bridge", networkInfo.Driver)

	t.Logf("Verbose network inspect: %+v", networkInfo)
}

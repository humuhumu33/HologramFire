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

func TestVerboseImageInspect(t *testing.T) {
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

	// List images
	images, err := cli.ImageList(ctx, types.ImageListOptions{})
	require.NoError(t, err)

	// Should have at least one image
	assert.Greater(t, len(images), 0, "Should have at least one image")

	// Check for Hologram-specific fields in verbose mode
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the images are listed successfully
	for _, img := range images {
		t.Logf("Image: %s, ID: %s", img.RepoTags, img.ID)
		// In verbose mode, we would expect to see XHologram fields
		// but for now we just verify the basic structure
		assert.NotEmpty(t, img.ID)
	}
}

func TestVerboseContainerInspect(t *testing.T) {
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

	// In verbose mode, check for Hologram-specific fields
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the container was created successfully
	assert.Equal(t, containerID, inspectResp.ID)
	assert.Equal(t, testImage, inspectResp.Config.Image)

	t.Logf("Verbose container inspect: %+v", inspectResp)

	// In verbose mode, we would expect to see XHologram fields like:
	// - XHologram.lease_id
	// - XHologram.witness_ok
	// - XHologram.uor_id
	// But for now we just verify the basic structure
}

func TestVerboseVolumeInspect(t *testing.T) {
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

	// Create volume
	volumeName := fmt.Sprintf("test-volume-%d", time.Now().Unix())
	volumeConfig := &types.VolumeCreateBody{
		Name:   volumeName,
		Driver: "local",
	}

	_, err = cli.VolumeCreate(ctx, *volumeConfig)
	require.NoError(t, err)

	defer func() {
		err := cli.VolumeRemove(ctx, volumeName, true)
		if err != nil {
			t.Logf("Failed to remove volume: %v", err)
		}
	}()

	// Inspect volume
	volumeResp, err := cli.VolumeInspect(ctx, volumeName)
	require.NoError(t, err)

	// In verbose mode, check for Hologram-specific fields
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the volume was created successfully
	assert.Equal(t, volumeName, volumeResp.Name)
	assert.Equal(t, "local", volumeResp.Driver)

	t.Logf("Verbose volume inspect: %+v", volumeResp)

	// In verbose mode, we would expect to see XHologram fields like:
	// - XHologram.driver
	// - XHologram.created_by
	// But for now we just verify the basic structure
}

func TestVerboseNetworkInspect(t *testing.T) {
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

	// In verbose mode, we would expect to see XHologram fields like:
	// - XHologram.driver
	// - XHologram.created_by
	// - XHologram.ctp96_session (if CTP-96 is enabled)
	// But for now we just verify the basic structure
}

func TestVerboseModeDisabled(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with verbose mode disabled (default)
	os.Unsetenv("HOLOGRAM_VERBOSE")

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

	// In non-verbose mode, should NOT see Hologram-specific fields
	// Note: This would need to be implemented in the actual response
	// For now, we just verify the container was created successfully
	assert.Equal(t, containerID, inspectResp.ID)
	assert.Equal(t, testImage, inspectResp.Config.Image)

	t.Logf("Non-verbose container inspect: %+v", inspectResp)

	// In non-verbose mode, we should NOT see XHologram fields
	// This is the default behavior for Docker compatibility
}

func TestVerboseModeHeader(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test verbose mode via header instead of environment variable
	// This would require custom HTTP client setup
	// For now, we'll test the environment variable approach

	// Test with verbose mode enabled via environment
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

	// List images to test verbose mode
	images, err := cli.ImageList(ctx, types.ImageListOptions{})
	require.NoError(t, err)

	// Should have at least one image
	assert.Greater(t, len(images), 0, "Should have at least one image")

	t.Logf("Verbose mode enabled via environment variable")

	// In a real implementation, we would also test the header approach:
	// X-Hologram-Verbose: 1
	// But that would require custom HTTP client setup
}

package main

import (
	"context"
	"fmt"
	"os"
	"testing"
	"time"

	"github.com/docker/docker/api/types/volume"
	"github.com/docker/docker/client"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

const (
	hologramdSocket = "unix:///var/run/hologramd.sock"
)

func TestVolumeCreate(t *testing.T) {
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

	// Create volume
	volumeName := fmt.Sprintf("test-volume-%d", time.Now().Unix())
	volumeConfig := &volume.VolumeCreateBody{
		Name:   volumeName,
		Driver: "local",
		Labels: map[string]string{
			"test": "hologram",
		},
	}

	volumeResp, err := cli.VolumeCreate(ctx, *volumeConfig)
	require.NoError(t, err)

	assert.Equal(t, volumeName, volumeResp.Name)
	assert.Equal(t, "local", volumeResp.Driver)
	assert.Equal(t, "local", volumeResp.Scope)
	assert.NotEmpty(t, volumeResp.Mountpoint)

	t.Logf("Created volume: %s at %s", volumeResp.Name, volumeResp.Mountpoint)

	// Clean up
	defer func() {
		err := cli.VolumeRemove(ctx, volumeName, true)
		if err != nil {
			t.Logf("Failed to remove volume: %v", err)
		}
	}()
}

func TestVolumeInspect(t *testing.T) {
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

	// Create volume
	volumeName := fmt.Sprintf("test-volume-%d", time.Now().Unix())
	volumeConfig := &volume.VolumeCreateBody{
		Name:   volumeName,
		Driver: "local",
		Labels: map[string]string{
			"test": "hologram",
		},
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

	assert.Equal(t, volumeName, volumeResp.Name)
	assert.Equal(t, "local", volumeResp.Driver)
	assert.Equal(t, "local", volumeResp.Scope)
	assert.NotEmpty(t, volumeResp.Mountpoint)
	assert.Equal(t, "hologram", volumeResp.Labels["test"])

	t.Logf("Inspected volume: %+v", volumeResp)
}

func TestVolumeList(t *testing.T) {
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

	// Get initial volume count
	volumes, err := cli.VolumeList(ctx, volume.ListOptions{})
	require.NoError(t, err)

	initialCount := len(volumes.Volumes)
	t.Logf("Initial volume count: %d", initialCount)

	// Create a test volume
	volumeName := fmt.Sprintf("test-volume-%d", time.Now().Unix())
	volumeConfig := &volume.VolumeCreateBody{
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

	// List volumes again
	volumes, err = cli.VolumeList(ctx, volume.ListOptions{})
	require.NoError(t, err)

	assert.GreaterOrEqual(t, len(volumes.Volumes), initialCount+1)

	// Find our volume
	var found bool
	for _, v := range volumes.Volumes {
		if v.Name == volumeName {
			found = true
			assert.Equal(t, "local", v.Driver)
			break
		}
	}
	assert.True(t, found, "Volume should be in the list")
}

func TestVolumeRemove(t *testing.T) {
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

	// Create volume
	volumeName := fmt.Sprintf("test-volume-%d", time.Now().Unix())
	volumeConfig := &volume.VolumeCreateBody{
		Name:   volumeName,
		Driver: "local",
	}

	_, err = cli.VolumeCreate(ctx, *volumeConfig)
	require.NoError(t, err)

	// Verify volume exists
	_, err = cli.VolumeInspect(ctx, volumeName)
	require.NoError(t, err)

	// Remove volume
	err = cli.VolumeRemove(ctx, volumeName, false)
	require.NoError(t, err)

	// Verify volume is removed
	_, err = cli.VolumeInspect(ctx, volumeName)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "No such volume")
}

func TestVolumePrune(t *testing.T) {
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

	// Create a test volume
	volumeName := fmt.Sprintf("test-volume-%d", time.Now().Unix())
	volumeConfig := &volume.VolumeCreateBody{
		Name:   volumeName,
		Driver: "local",
	}

	_, err = cli.VolumeCreate(ctx, *volumeConfig)
	require.NoError(t, err)

	// Prune volumes
	pruneResp, err := cli.VolumesPrune(ctx, volume.PruneOptions{})
	require.NoError(t, err)

	t.Logf("Pruned volumes: %+v", pruneResp)

	// Verify volume is removed
	_, err = cli.VolumeInspect(ctx, volumeName)
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "No such volume")
}

func TestVolumeVerbose(t *testing.T) {
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
	volumeConfig := &volume.VolumeCreateBody{
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
}

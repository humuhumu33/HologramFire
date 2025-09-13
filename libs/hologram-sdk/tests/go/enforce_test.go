package main

import (
	"context"
	"os"
	"testing"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/client"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

const (
	hologramdSocket = "unix:///var/run/hologramd.sock"
)

func TestEnforceMode(t *testing.T) {
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

	// Test 1: Try to create container with "bad" image (should fail)
	containerConfig := &container.Config{
		Image: "holo-test-bad:latest",
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	_, err = cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "artifact witness invalid or missing")

	t.Logf("Enforce mode correctly rejected bad image: %v", err)

	// Test 2: Try to create container with "good" image (should succeed)
	containerConfig = &container.Config{
		Image: "alpine:latest",
		Cmd:   []string{"echo", "test"},
	}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	t.Logf("Enforce mode correctly allowed good image: %s", containerID)

	// Clean up
	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()
}

func TestEnforceModeDisabled(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with enforce mode disabled (default)
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Test: Try to create container with "bad" image (should succeed in permissive mode)
	containerConfig := &container.Config{
		Image: "holo-test-bad:latest",
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	t.Logf("Permissive mode allowed bad image: %s", containerID)

	// Clean up
	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()
}

func TestEnforceModeWithWarnings(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with enforce mode enabled but with warnings
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

	// Test: Try to create container with image that has missing witness (should fail)
	containerConfig := &container.Config{
		Image: "missing-witness:latest",
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	_, err = cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "artifact witness invalid or missing")

	t.Logf("Enforce mode correctly rejected missing witness: %v", err)
}

func TestEnforceModeImagePull(t *testing.T) {
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

	// Test: Try to pull "bad" image (should fail in enforce mode)
	_, err = cli.ImagePull(ctx, "holo-test-bad:latest", types.ImagePullOptions{})
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "artifact witness invalid or missing")

	t.Logf("Enforce mode correctly rejected bad image pull: %v", err)

	// Test: Try to pull "good" image (should succeed)
	_, err = cli.ImagePull(ctx, "alpine:latest", types.ImagePullOptions{})
	// Note: This might fail for other reasons (network, etc.), but shouldn't fail due to enforce mode
	if err != nil {
		t.Logf("Image pull failed (possibly due to network): %v", err)
	} else {
		t.Logf("Enforce mode correctly allowed good image pull")
	}
}

func TestEnforceModeContainerStart(t *testing.T) {
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

	// Create container with "bad" image (should fail in enforce mode)
	containerConfig := &container.Config{
		Image: "holo-test-bad:latest",
		Cmd:   []string{"echo", "test"},
	}

	hostConfig := &container.HostConfig{}

	_, err = cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	assert.Error(t, err)
	assert.Contains(t, err.Error(), "artifact witness invalid or missing")

	t.Logf("Enforce mode correctly rejected bad image on create: %v", err)

	// Create container with "good" image
	containerConfig = &container.Config{
		Image: "alpine:latest",
		Cmd:   []string{"echo", "test"},
	}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(t, err)
	containerID := createResp.ID

	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()

	// Start container (should succeed)
	err = cli.ContainerStart(ctx, containerID, types.ContainerStartOptions{})
	require.NoError(t, err)

	t.Logf("Enforce mode correctly allowed good image on start")
}

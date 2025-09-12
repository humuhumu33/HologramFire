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
	"github.com/stretchr/testify/require"
)

const (
	hologramdSocket = "unix:///var/run/hologramd.sock"
	testImage       = "alpine:latest"
)

func BenchmarkContainerStart(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Pre-create containers for benchmarking
	containers := make([]string, b.N)
	for i := 0; i < b.N; i++ {
		containerConfig := &container.Config{
			Image: testImage,
			Cmd:   []string{"echo", "benchmark"},
		}

		hostConfig := &container.HostConfig{}

		createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
		require.NoError(b, err)
		containers[i] = createResp.ID
	}

	// Clean up containers after benchmark
	defer func() {
		for _, containerID := range containers {
			cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
		}
	}()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark container start
	for i := 0; i < b.N; i++ {
		start := time.Now()

		err := cli.ContainerStart(ctx, containers[i], types.ContainerStartOptions{})
		require.NoError(b, err)

		// Stop container immediately
		timeout := 1
		cli.ContainerStop(ctx, containers[i], container.StopOptions{
			Timeout: &timeout,
		})

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/start")
	}
}

func BenchmarkContainerCreate(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Clean up containers after benchmark
	var containers []string
	defer func() {
		for _, containerID := range containers {
			cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
		}
	}()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark container creation
	for i := 0; i < b.N; i++ {
		start := time.Now()

		containerConfig := &container.Config{
			Image: testImage,
			Cmd:   []string{"echo", "benchmark"},
		}

		hostConfig := &container.HostConfig{}

		createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
		require.NoError(b, err)

		containers = append(containers, createResp.ID)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/create")
	}
}

func BenchmarkContainerInspect(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Create a container for benchmarking
	containerConfig := &container.Config{
		Image: testImage,
		Cmd:   []string{"echo", "benchmark"},
	}

	hostConfig := &container.HostConfig{}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
	require.NoError(b, err)
	containerID := createResp.ID

	defer func() {
		cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
	}()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark container inspect
	for i := 0; i < b.N; i++ {
		start := time.Now()

		_, err := cli.ContainerInspect(ctx, containerID)
		require.NoError(b, err)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/inspect")
	}
}

func BenchmarkContainerList(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Create some containers for benchmarking
	containers := make([]string, 10)
	for i := 0; i < 10; i++ {
		containerConfig := &container.Config{
			Image: testImage,
			Cmd:   []string{"echo", "benchmark"},
		}

		hostConfig := &container.HostConfig{}

		createResp, err := cli.ContainerCreate(ctx, containerConfig, hostConfig, nil, nil, "")
		require.NoError(b, err)
		containers[i] = createResp.ID
	}

	defer func() {
		for _, containerID := range containers {
			cli.ContainerRemove(ctx, containerID, types.ContainerRemoveOptions{Force: true})
		}
	}()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark container list
	for i := 0; i < b.N; i++ {
		start := time.Now()

		_, err := cli.ContainerList(ctx, types.ContainerListOptions{All: true})
		require.NoError(b, err)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/list")
	}
}

func BenchmarkVolumeCreate(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Clean up volumes after benchmark
	var volumes []string
	defer func() {
		for _, volumeName := range volumes {
			cli.VolumeRemove(ctx, volumeName, true)
		}
	}()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark volume creation
	for i := 0; i < b.N; i++ {
		start := time.Now()

		volumeName := fmt.Sprintf("bench-volume-%d-%d", time.Now().Unix(), i)
		volumeConfig := &types.VolumeCreateBody{
			Name:   volumeName,
			Driver: "local",
		}

		_, err := cli.VolumeCreate(ctx, *volumeConfig)
		require.NoError(b, err)

		volumes = append(volumes, volumeName)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/volume-create")
	}
}

func BenchmarkNetworkCreate(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Clean up networks after benchmark
	var networks []string
	defer func() {
		for _, networkID := range networks {
			cli.NetworkRemove(ctx, networkID)
		}
	}()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark network creation
	for i := 0; i < b.N; i++ {
		start := time.Now()

		networkName := fmt.Sprintf("bench-network-%d-%d", time.Now().Unix(), i)
		networkConfig := &types.NetworkCreate{
			Name:   networkName,
			Driver: "bridge",
		}

		networkResp, err := cli.NetworkCreate(ctx, networkName, *networkConfig)
		require.NoError(b, err)

		networks = append(networks, networkResp.ID)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/network-create")
	}
}

func BenchmarkImageList(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark image list
	for i := 0; i < b.N; i++ {
		start := time.Now()

		_, err := cli.ImageList(ctx, types.ImageListOptions{})
		require.NoError(b, err)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/image-list")
	}
}

func BenchmarkVersion(b *testing.B) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		b.Skip("Skipping hologramd-specific tests")
	}

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(b, err)
	defer cli.Close()

	ctx := context.Background()

	// Reset timer to exclude setup time
	b.ResetTimer()

	// Benchmark version endpoint
	for i := 0; i < b.N; i++ {
		start := time.Now()

		_, err := cli.ServerVersion(ctx)
		require.NoError(b, err)

		duration := time.Since(start)
		b.ReportMetric(float64(duration.Nanoseconds())/1e6, "ms/version")
	}
}

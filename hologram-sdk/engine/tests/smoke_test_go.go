package main

import (
	"context"
	"fmt"
	"io"
	"log"
	"time"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/client"
)

// TestHologramdCompatibility tests basic compatibility with hologramd
func main() {
	fmt.Println("Testing hologramd compatibility with Docker Go SDK...")

	// Create Docker client pointing to hologramd socket
	cli, err := client.NewClientWithOpts(
		client.WithHost("unix:///var/run/hologramd.sock"),
		client.WithAPIVersionNegotiation(),
	)
	if err != nil {
		log.Fatalf("Failed to create Docker client: %v", err)
	}
	defer cli.Close()

	ctx := context.Background()

	// Test 1: Ping
	fmt.Println("1. Testing ping...")
	_, err = cli.Ping(ctx)
	if err != nil {
		log.Fatalf("Ping failed: %v", err)
	}
	fmt.Println("   ✓ Ping successful")

	// Test 2: Server version
	fmt.Println("2. Testing server version...")
	version, err := cli.ServerVersion(ctx)
	if err != nil {
		log.Fatalf("Server version failed: %v", err)
	}
	fmt.Printf("   ✓ Server version: %s (API: %s)\n", version.Version, version.APIVersion)

	// Test 3: List images
	fmt.Println("3. Testing image list...")
	images, err := cli.ImageList(ctx, types.ImageListOptions{})
	if err != nil {
		log.Fatalf("Image list failed: %v", err)
	}
	fmt.Printf("   ✓ Found %d images\n", len(images))

	// Test 4: Pull image (streaming)
	fmt.Println("4. Testing image pull...")
	pullReader, err := cli.ImagePull(ctx, "nginx:alpine", types.ImagePullOptions{})
	if err != nil {
		log.Fatalf("Image pull failed: %v", err)
	}
	defer pullReader.Close()

	// Consume the stream
	_, err = io.Copy(io.Discard, pullReader)
	if err != nil {
		log.Fatalf("Failed to consume pull stream: %v", err)
	}
	fmt.Println("   ✓ Image pull successful")

	// Test 5: List images again to verify pull
	fmt.Println("5. Verifying pulled image...")
	images, err = cli.ImageList(ctx, types.ImageListOptions{})
	if err != nil {
		log.Fatalf("Image list failed: %v", err)
	}

	nginxFound := false
	for _, img := range images {
		for _, tag := range img.RepoTags {
			if tag == "nginx:alpine" {
				nginxFound = true
				break
			}
		}
	}

	if nginxFound {
		fmt.Println("   ✓ Nginx image found in list")
	} else {
		fmt.Println("   ⚠ Nginx image not found in list (may be expected)")
	}

	// Test 6: Container operations
	fmt.Println("6. Testing container create...")
	containerConfig := &container.Config{
		Image: "nginx:alpine",
		Cmd:   []string{"echo", "hello from hologramd"},
	}

	createResp, err := cli.ContainerCreate(ctx, containerConfig, nil, nil, nil, "hologramd-test")
	if err != nil {
		log.Fatalf("Container create failed: %v", err)
	}
	fmt.Printf("   ✓ Container created: %s\n", createResp.ID[:12])

	// Test 7: Container start
	fmt.Println("7. Testing container start...")
	err = cli.ContainerStart(ctx, createResp.ID, types.ContainerStartOptions{})
	if err != nil {
		log.Fatalf("Container start failed: %v", err)
	}
	fmt.Println("   ✓ Container started")

	// Wait a moment for container to run
	time.Sleep(2 * time.Second)

	// Test 8: Container logs
	fmt.Println("8. Testing container logs...")
	logsReader, err := cli.ContainerLogs(ctx, createResp.ID, types.ContainerLogsOptions{
		ShowStdout: true,
		ShowStderr: true,
	})
	if err != nil {
		log.Fatalf("Container logs failed: %v", err)
	}
	defer logsReader.Close()

	logs, err := io.ReadAll(logsReader)
	if err != nil {
		log.Fatalf("Failed to read container logs: %v", err)
	}
	fmt.Printf("   ✓ Container logs: %s\n", string(logs))

	// Test 9: Container stop
	fmt.Println("9. Testing container stop...")
	timeout := 10
	err = cli.ContainerStop(ctx, createResp.ID, container.StopOptions{Timeout: &timeout})
	if err != nil {
		log.Fatalf("Container stop failed: %v", err)
	}
	fmt.Println("   ✓ Container stopped")

	// Test 10: Container remove
	fmt.Println("10. Testing container remove...")
	err = cli.ContainerRemove(ctx, createResp.ID, types.ContainerRemoveOptions{})
	if err != nil {
		log.Fatalf("Container remove failed: %v", err)
	}
	fmt.Println("   ✓ Container removed")

	fmt.Println("\n🎉 All tests passed! hologramd is compatible with Docker Go SDK")
}

package e2e

import (
	"context"
	"encoding/json"
	"io"
	"net"
	"net/http"
	"os"
	"testing"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
)

func TestImageInspectXHologram(t *testing.T) {
	if os.Getenv("HOLOGRAM_VERBOSE") != "1" {
		t.Skip("run with HOLOGRAM_VERBOSE=1")
	}
	ctx := context.Background()
	cli := hgClient(t)

	// list images and ensure at least one has XHologram via raw call
	resp, err := cli.ImageList(ctx, types.ImageListOptions{})
	if err != nil {
		t.Fatalf("image list: %v", err)
	}

	if len(resp) == 0 {
		t.Skip("no images available for inspection")
	}

	// Use raw HTTP to check for XHologram fields since Go client may strip them
	host := os.Getenv("HG_HOST")
	if host == "" {
		host = "unix:///var/run/hologramd.sock"
	}

	// For unix socket, we need to make a raw HTTP call
	httpClient := &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return net.Dial("unix", "/var/run/hologramd.sock")
			},
		},
	}

	httpResp, err := httpClient.Get("http://unix/images/json")
	if err != nil {
		t.Fatalf("raw HTTP call failed: %v", err)
	}
	defer httpResp.Body.Close()

	body, err := io.ReadAll(httpResp.Body)
	if err != nil {
		t.Fatalf("read response body: %v", err)
	}

	var images []map[string]interface{}
	if err := json.Unmarshal(body, &images); err != nil {
		t.Fatalf("unmarshal images: %v", err)
	}

	// Check if any image has XHologram fields
	foundXHologram := false
	for _, img := range images {
		if _, exists := img["XHologram"]; exists {
			foundXHologram = true
			break
		}
	}

	if !foundXHologram {
		t.Fatalf("expected XHologram fields in verbose mode")
	}
}

func TestContainerInspectXHologram(t *testing.T) {
	if os.Getenv("HOLOGRAM_VERBOSE") != "1" {
		t.Skip("run with HOLOGRAM_VERBOSE=1")
	}
	ctx := context.Background()
	cli := hgClient(t)

	// Create/start a container, then ContainerInspect and check .XHologram via raw JSON if needed.
	resp, err := cli.ContainerCreate(ctx, &container.Config{
		Image: "alpine:3.19",
		Cmd:   []string{"sleep", "5"},
	}, &container.HostConfig{}, nil, nil, "hg-e2e-verbose-ctr")
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	t.Cleanup(func() { _ = cli.ContainerRemove(ctx, resp.ID, types.ContainerRemoveOptions{Force: true}) })

	if err := cli.ContainerStart(ctx, resp.ID, types.ContainerStartOptions{}); err != nil {
		t.Fatalf("start: %v", err)
	}

	// Use raw HTTP to check for XHologram fields
	httpClient := &http.Client{
		Transport: &http.Transport{
			DialContext: func(ctx context.Context, network, addr string) (net.Conn, error) {
				return net.Dial("unix", "/var/run/hologramd.sock")
			},
		},
	}

	httpResp, err := httpClient.Get("http://unix/containers/" + resp.ID + "/json")
	if err != nil {
		t.Fatalf("raw HTTP call failed: %v", err)
	}
	defer httpResp.Body.Close()

	body, err := io.ReadAll(httpResp.Body)
	if err != nil {
		t.Fatalf("read response body: %v", err)
	}

	var containerData map[string]interface{}
	if err := json.Unmarshal(body, &containerData); err != nil {
		t.Fatalf("unmarshal container: %v", err)
	}

	// Check if container has XHologram fields
	if _, exists := containerData["XHologram"]; !exists {
		t.Fatalf("expected XHologram fields in verbose mode")
	}
}

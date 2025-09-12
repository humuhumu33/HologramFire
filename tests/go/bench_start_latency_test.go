package e2e

import (
	"context"
	"testing"
	"time"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
)

func BenchmarkStartLatency(b *testing.B) {
	ctx := context.Background()
	cli := hgClient(&testing.T{})

	for i := 0; i < b.N; i++ {
		resp, _ := cli.ContainerCreate(ctx, &container.Config{
			Image: "alpine:3.19",
			Cmd:   []string{"true"},
		}, nil, nil, nil, "")
		t0 := time.Now()
		_ = cli.ContainerStart(ctx, resp.ID, types.ContainerStartOptions{})
		_ = cli.ContainerRemove(ctx, resp.ID, types.ContainerRemoveOptions{Force: true})
		b.ReportMetric(float64(time.Since(t0).Milliseconds()), "ms/start")
	}
}

func BenchmarkImagePullLatency(b *testing.B) {
	ctx := context.Background()
	cli := hgClient(&testing.T{})

	for i := 0; i < b.N; i++ {
		t0 := time.Now()
		r, err := cli.ImagePull(ctx, "docker.io/library/alpine:3.19", types.ImagePullOptions{})
		if err != nil {
			b.Fatalf("image pull failed: %v", err)
		}
		r.Close()
		b.ReportMetric(float64(time.Since(t0).Milliseconds()), "ms/pull")
	}
}

func BenchmarkContainerInspectLatency(b *testing.B) {
	ctx := context.Background()
	cli := hgClient(&testing.T{})

	// Create a container once
	resp, err := cli.ContainerCreate(ctx, &container.Config{
		Image: "alpine:3.19",
		Cmd:   []string{"sleep", "60"},
	}, nil, nil, nil, "")
	if err != nil {
		b.Fatalf("container create failed: %v", err)
	}
	defer cli.ContainerRemove(ctx, resp.ID, types.ContainerRemoveOptions{Force: true})

	if err := cli.ContainerStart(ctx, resp.ID, types.ContainerStartOptions{}); err != nil {
		b.Fatalf("container start failed: %v", err)
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		t0 := time.Now()
		_, err := cli.ContainerInspect(ctx, resp.ID)
		if err != nil {
			b.Fatalf("container inspect failed: %v", err)
		}
		b.ReportMetric(float64(time.Since(t0).Milliseconds()), "ms/inspect")
	}
}

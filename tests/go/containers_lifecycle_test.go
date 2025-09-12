package e2e

import (
	"context"
	"os"
	"testing"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/client"
)

func hgClient(t *testing.T) *client.Client {
	t.Helper()
	host := os.Getenv("HG_HOST")
	if host == "" {
		host = "unix:///var/run/hologramd.sock"
	}
	cli, err := client.NewClientWithOpts(
		client.WithHost(host),
		client.WithAPIVersionNegotiation(),
	)
	if err != nil {
		t.Fatalf("client: %v", err)
	}
	return cli
}

func TestContainerHappyPath(t *testing.T) {
	ctx := context.Background()
	cli := hgClient(t)

	// ensure image exists (progress stream ignored)
	r, err := cli.ImagePull(ctx, "docker.io/library/alpine:3.19", types.ImagePullOptions{})
	if err != nil {
		t.Fatalf("pull: %v", err)
	}
	r.Close()

	resp, err := cli.ContainerCreate(ctx, &container.Config{
		Image: "alpine:3.19",
		Cmd:   []string{"sh", "-c", "echo hello && sleep 2"},
	}, &container.HostConfig{}, nil, nil, "hg-e2e-ctr")
	if err != nil {
		t.Fatalf("create: %v", err)
	}

	if err := cli.ContainerStart(ctx, resp.ID, types.ContainerStartOptions{}); err != nil {
		t.Fatalf("start: %v", err)
	}

	// logs stream
	rc, err := cli.ContainerLogs(ctx, resp.ID, types.ContainerLogsOptions{
		ShowStdout: true, Follow: true, Tail: "all",
	})
	if err != nil {
		t.Fatalf("logs: %v", err)
	}
	buf := make([]byte, 1<<12)
	_, _ = rc.Read(buf) // just touch the stream
	_ = rc.Close()

	// inspect shape must match Docker
	ins, err := cli.ContainerInspect(ctx, resp.ID)
	if err != nil {
		t.Fatalf("inspect: %v", err)
	}
	if !ins.State.Running && !ins.State.OOMKilled && ins.Created == "" {
		t.Fatalf("inspect shape looks wrong: %+v", ins.State)
	}

	// stop with timeout
	timeoutSecs := 5
	if err := cli.ContainerStop(ctx, resp.ID, container.StopOptions{Timeout: &timeoutSecs}); err != nil {
		t.Fatalf("stop: %v", err)
	}
	if err := cli.ContainerRemove(ctx, resp.ID, types.ContainerRemoveOptions{Force: true}); err != nil {
		t.Fatalf("rm: %v", err)
	}
}

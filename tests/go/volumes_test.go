package e2e

import (
	"context"
	"testing"

	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/api/types/mount"
	"github.com/docker/docker/api/types/volume"
)

func TestVolumesNamedAndBind(t *testing.T) {
	ctx := context.Background()
	cli := hgClient(t)

	// named volume
	vol, err := cli.VolumeCreate(ctx, volume.CreateOptions{Name: "hg-e2e-volume"})
	if err != nil {
		t.Fatalf("vol create: %v", err)
	}
	t.Cleanup(func() { _ = cli.VolumeRemove(ctx, vol.Name, true) })

	// run alpine with named volume and a bind mount (if supported)
	resp, err := cli.ContainerCreate(ctx, &container.Config{
		Image: "alpine:3.19",
		Cmd:   []string{"sh", "-c", "echo ok > /data/ok.txt && sleep 1"},
	}, &container.HostConfig{
		Binds:       []string{"/tmp:/hosttmp:rw"},
		VolumesFrom: nil,
		Mounts: []mount.Mount{
			{Type: mount.TypeVolume, Source: vol.Name, Target: "/data"},
		},
	}, nil, nil, "")
	if err != nil {
		t.Fatalf("ctr create: %v", err)
	}
	_ = resp
}

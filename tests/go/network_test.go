package e2e

import (
	"context"
	"os"
	"testing"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/container"
	"github.com/docker/docker/api/types/network"
)

func TestBridgeNetworkCreateConnect(t *testing.T) {
	ctx := context.Background()
	cli := hgClient(t)

	resp, err := cli.NetworkCreate(ctx, "hg-e2e-net", types.NetworkCreate{Driver: "bridge"})
	if err != nil {
		t.Fatalf("net create: %v", err)
	}
	t.Cleanup(func() { _ = cli.NetworkRemove(ctx, resp.ID) })

	// create a container and connect
	ctrResp, err := cli.ContainerCreate(ctx, &container.Config{
		Image: "alpine:3.19",
		Cmd:   []string{"sleep", "10"},
	}, &container.HostConfig{}, nil, nil, "hg-e2e-net-ctr")
	if err != nil {
		t.Fatalf("ctr create: %v", err)
	}
	t.Cleanup(func() { _ = cli.ContainerRemove(ctx, ctrResp.ID, types.ContainerRemoveOptions{Force: true}) })

	err = cli.NetworkConnect(ctx, resp.ID, ctrResp.ID, &network.EndpointSettings{})
	if err != nil {
		t.Fatalf("net connect: %v", err)
	}
}

func TestCTP96OptInDoesNotBreakUX(t *testing.T) {
	if os.Getenv("HOLOGRAM_NET") != "ctp96" {
		t.Skip("run with HOLOGRAM_NET=ctp96 to validate optional driver")
	}
	ctx := context.Background()
	cli := hgClient(t)

	// same flow as above, expecting normal Docker UX + (optional) XHologram ctp96_session in inspect
	resp, err := cli.NetworkCreate(ctx, "hg-e2e-ctp96-net", types.NetworkCreate{Driver: "bridge"})
	if err != nil {
		t.Fatalf("ctp96 net create: %v", err)
	}
	t.Cleanup(func() { _ = cli.NetworkRemove(ctx, resp.ID) })

	// inspect should have normal Docker shape + optional XHologram fields
	netInspect, err := cli.NetworkInspect(ctx, resp.ID, types.NetworkInspectOptions{})
	if err != nil {
		t.Fatalf("ctp96 net inspect: %v", err)
	}

	// Basic Docker shape validation
	if netInspect.Name != "hg-e2e-ctp96-net" {
		t.Fatalf("expected network name hg-e2e-ctp96-net, got %s", netInspect.Name)
	}
}

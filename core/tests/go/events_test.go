package e2e

import (
	"context"
	"os"
	"testing"
	"time"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/filters"
)

func TestEventsLifecycle(t *testing.T) {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	cli := hgClient(t)

	f := filters.NewArgs()
	f.Add("type", "container")
	msgs, errs := cli.Events(ctx, types.EventsOptions{Filters: f})

	// trigger something small (ps is enough once lifecycle tests exist)
	count := 0
	for count < 1 {
		select {
		case ev := <-msgs:
			if ev.Type == "container" && (ev.Action == "create" || ev.Action == "start" || ev.Action == "stop") {
				// in verbose mode we allow XHologram.* attributes, but they must be optional
				_ = ev.Actor.Attributes // should exist as map
				count++
			}
		case err := <-errs:
			if err != nil {
				t.Fatalf("events err: %v", err)
			}
		case <-ctx.Done():
			t.Fatal("timeout waiting for events")
		}
	}
	_ = os.Stdout
}

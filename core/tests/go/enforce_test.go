package e2e

import (
	"context"
	"os"
	"strings"
	"testing"

	"github.com/docker/docker/api/types"
)

func TestEnforceRejectsInvalidWitness(t *testing.T) {
	if os.Getenv("HOLOGRAM_ENFORCE") != "1" {
		t.Skip("run with HOLOGRAM_ENFORCE=1")
	}
	ctx := context.Background()
	cli := hgClient(t)

	// Use test knob for deterministic bad witness
	// "holo-test-bad:*" -> "uor:test/bad:*" -> always fails witness verification
	_, err := cli.ImagePull(ctx, "holo-test-bad:latest", types.ImagePullOptions{})
	if err == nil {
		t.Fatalf("expected witness enforcement error")
	}

	// The docker client error wraps the JSON; asserting string contains is acceptable for now.
	errStr := err.Error()
	if !strings.Contains(errStr, "witness") && !strings.Contains(errStr, "enforce") && !strings.Contains(errStr, "invalid") {
		t.Fatalf("expected enforcement error message, got: %s", errStr)
	}
}

func TestEnforceAllowsValidWitness(t *testing.T) {
	if os.Getenv("HOLOGRAM_ENFORCE") != "1" {
		t.Skip("run with HOLOGRAM_ENFORCE=1")
	}
	ctx := context.Background()
	cli := hgClient(t)

	// Use test knob for deterministic good witness
	// "holo-test-ok:*" -> "uor:test/ok:*" -> always passes witness verification
	r, err := cli.ImagePull(ctx, "holo-test-ok:latest", types.ImagePullOptions{})
	if err != nil {
		t.Fatalf("expected valid witness to pass, got: %v", err)
	}
	r.Close()
}

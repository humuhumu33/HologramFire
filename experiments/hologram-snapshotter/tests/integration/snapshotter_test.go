package integration

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/containerd/containerd"
	"github.com/containerd/containerd/namespaces"
	"github.com/containerd/containerd/snapshots"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/hologram/hologram-snapshotter/pkg/snapshotter"
)

func TestHologramSnapshotter(t *testing.T) {
	// Create test client
	client, err := containerd.New("/run/containerd/containerd.sock")
	require.NoError(t, err)
	defer client.Close()

	// Create test namespace
	ctx := namespaces.WithNamespace(context.Background(), "hologram-test")

	// Create snapshotter
	config := &snapshotter.Config{
		Root:    filepath.Join(os.TempDir(), "hologram-test"),
		Enforce: false,
		Verbose: true,
		Client:  client,
	}

	snapshotterInstance, err := snapshotter.NewSnapshotter(config)
	require.NoError(t, err)
	defer snapshotterInstance.Close()

	t.Run("Prepare", func(t *testing.T) {
		key := "test-prepare"
		parent := ""

		mounts, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)
		assert.NotEmpty(t, mounts)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, key)
		require.NoError(t, err)
	})

	t.Run("Commit", func(t *testing.T) {
		key := "test-commit"
		parent := ""

		// Prepare
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)

		// Commit
		err = snapshotterInstance.Commit(ctx, "test-committed", key)
		require.NoError(t, err)

		// Verify committed snapshot exists
		info, err := snapshotterInstance.Stat(ctx, "test-committed")
		require.NoError(t, err)
		assert.Equal(t, "test-committed", info.Name)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, "test-committed")
		require.NoError(t, err)
	})

	t.Run("View", func(t *testing.T) {
		key := "test-view"
		parent := ""

		// Prepare and commit
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)
		err = snapshotterInstance.Commit(ctx, "test-view-committed", key)
		require.NoError(t, err)

		// Create view
		mounts, err := snapshotterInstance.View(ctx, "test-view-view", "test-view-committed")
		require.NoError(t, err)
		assert.NotEmpty(t, mounts)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, "test-view-committed")
		require.NoError(t, err)
		err = snapshotterInstance.Remove(ctx, "test-view-view")
		require.NoError(t, err)
	})

	t.Run("Mounts", func(t *testing.T) {
		key := "test-mounts"
		parent := ""

		// Prepare
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)

		// Get mounts
		mounts, err := snapshotterInstance.Mounts(ctx, key)
		require.NoError(t, err)
		assert.NotEmpty(t, mounts)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, key)
		require.NoError(t, err)
	})

	t.Run("Usage", func(t *testing.T) {
		key := "test-usage"
		parent := ""

		// Prepare
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)

		// Get usage
		usage, err := snapshotterInstance.Usage(ctx, key)
		require.NoError(t, err)
		assert.NotNil(t, usage)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, key)
		require.NoError(t, err)
	})

	t.Run("Walk", func(t *testing.T) {
		key := "test-walk"
		parent := ""

		// Prepare and commit
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)
		err = snapshotterInstance.Commit(ctx, "test-walk-committed", key)
		require.NoError(t, err)

		// Walk snapshots
		var found []snapshots.Info
		err = snapshotterInstance.Walk(ctx, func(ctx context.Context, info snapshots.Info) error {
			found = append(found, info)
			return nil
		})
		require.NoError(t, err)
		assert.NotEmpty(t, found)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, "test-walk-committed")
		require.NoError(t, err)
	})
}

func TestHologramSnapshotterEnforceMode(t *testing.T) {
	// Set enforce mode
	os.Setenv("HOLOGRAM_ENFORCE", "true")
	defer os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create test client
	client, err := containerd.New("/run/containerd/containerd.sock")
	require.NoError(t, err)
	defer client.Close()

	// Create test namespace
	ctx := namespaces.WithNamespace(context.Background(), "hologram-enforce-test")

	// Create snapshotter with enforce mode
	config := &snapshotter.Config{
		Root:    filepath.Join(os.TempDir(), "hologram-enforce-test"),
		Enforce: true,
		Verbose: true,
		Client:  client,
	}

	snapshotterInstance, err := snapshotter.NewSnapshotter(config)
	require.NoError(t, err)
	defer snapshotterInstance.Close()

	t.Run("EnforceModeEnabled", func(t *testing.T) {
		// In enforce mode, operations should still work but with additional validation
		key := "test-enforce"
		parent := ""

		mounts, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)
		assert.NotEmpty(t, mounts)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, key)
		require.NoError(t, err)
	})
}

func TestHologramSnapshotterVerboseMode(t *testing.T) {
	// Set verbose mode
	os.Setenv("HOLOGRAM_VERBOSE", "true")
	defer os.Unsetenv("HOLOGRAM_VERBOSE")

	// Create test client
	client, err := containerd.New("/run/containerd/containerd.sock")
	require.NoError(t, err)
	defer client.Close()

	// Create test namespace
	ctx := namespaces.WithNamespace(context.Background(), "hologram-verbose-test")

	// Create snapshotter with verbose mode
	config := &snapshotter.Config{
		Root:    filepath.Join(os.TempDir(), "hologram-verbose-test"),
		Enforce: false,
		Verbose: true,
		Client:  client,
	}

	snapshotterInstance, err := snapshotter.NewSnapshotter(config)
	require.NoError(t, err)
	defer snapshotterInstance.Close()

	t.Run("VerboseModeEnabled", func(t *testing.T) {
		// In verbose mode, operations should include additional metadata
		key := "test-verbose"
		parent := ""

		mounts, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)
		assert.NotEmpty(t, mounts)

		// Cleanup
		err = snapshotterInstance.Remove(ctx, key)
		require.NoError(t, err)
	})
}

func TestHologramSnapshotterPerformance(t *testing.T) {
	// Create test client
	client, err := containerd.New("/run/containerd/containerd.sock")
	require.NoError(t, err)
	defer client.Close()

	// Create test namespace
	ctx := namespaces.WithNamespace(context.Background(), "hologram-perf-test")

	// Create snapshotter
	config := &snapshotter.Config{
		Root:    filepath.Join(os.TempDir(), "hologram-perf-test"),
		Enforce: false,
		Verbose: false,
		Client:  client,
	}

	snapshotterInstance, err := snapshotter.NewSnapshotter(config)
	require.NoError(t, err)
	defer snapshotterInstance.Close()

	t.Run("PreparePerformance", func(t *testing.T) {
		key := "test-perf-prepare"
		parent := ""

		start := time.Now()
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		duration := time.Since(start)

		require.NoError(t, err)
		assert.Less(t, duration, 5*time.Second, "Prepare should complete within 5 seconds")

		// Cleanup
		err = snapshotterInstance.Remove(ctx, key)
		require.NoError(t, err)
	})

	t.Run("CommitPerformance", func(t *testing.T) {
		key := "test-perf-commit"
		parent := ""

		// Prepare
		_, err := snapshotterInstance.Prepare(ctx, key, parent)
		require.NoError(t, err)

		// Commit
		start := time.Now()
		err = snapshotterInstance.Commit(ctx, "test-perf-committed", key)
		duration := time.Since(start)

		require.NoError(t, err)
		assert.Less(t, duration, 5*time.Second, "Commit should complete within 5 seconds")

		// Cleanup
		err = snapshotterInstance.Remove(ctx, "test-perf-committed")
		require.NoError(t, err)
	})
}

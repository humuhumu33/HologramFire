package snapshotter

import (
	"context"
	"fmt"
	"os"
	"path/filepath"
	"sync"

	"github.com/containerd/containerd"
	"github.com/containerd/containerd/errdefs"
	"github.com/containerd/containerd/log"
	"github.com/containerd/containerd/mount"
	"github.com/containerd/containerd/snapshots"
	"github.com/containerd/containerd/snapshots/storage"
	"github.com/opencontainers/go-digest"
	"github.com/opencontainers/image-spec/identity"

	"github.com/hologram/hologram-snapshotter/pkg/content"
	"github.com/hologram/hologram-snapshotter/pkg/fusefs"
	"github.com/hologram/hologram-snapshotter/pkg/resolver"
	"github.com/hologram/hologram-snapshotter/pkg/telemetry"
)

// Config holds configuration for the hologram snapshotter
type Config struct {
	Root    string
	Enforce bool
	Verbose bool
	Client  *containerd.Client
}

// Snapshotter implements the containerd snapshotter interface with FUSE backend
type Snapshotter struct {
	root      string
	enforce   bool
	verbose   bool
	client    *containerd.Client
	ms        *storage.MetaStore
	resolver  *resolver.Resolver
	content   *content.Store
	fuseFS    *fusefs.Filesystem
	telemetry *telemetry.Telemetry
	mu        sync.RWMutex
}

// NewSnapshotter creates a new hologram snapshotter instance
func NewSnapshotter(config *Config) (snapshots.Snapshotter, error) {
	root := filepath.Join(config.Root, "hologram")
	if err := os.MkdirAll(root, 0700); err != nil {
		return nil, fmt.Errorf("failed to create root directory: %w", err)
	}

	ms, err := storage.NewMetaStore(filepath.Join(root, "metadata.db"))
	if err != nil {
		return nil, fmt.Errorf("failed to create metastore: %w", err)
	}

	resolver, err := resolver.NewResolver(config.Client, config.Enforce, config.Verbose)
	if err != nil {
		return nil, fmt.Errorf("failed to create resolver: %w", err)
	}

	contentStore, err := content.NewStore(config.Client, root)
	if err != nil {
		return nil, fmt.Errorf("failed to create content store: %w", err)
	}

	fuseFS, err := fusefs.NewFilesystem(root, contentStore)
	if err != nil {
		return nil, fmt.Errorf("failed to create FUSE filesystem: %w", err)
	}

	telemetry := telemetry.NewTelemetry()

	return &Snapshotter{
		root:      root,
		enforce:   config.Enforce,
		verbose:   config.Verbose,
		client:    config.Client,
		ms:        ms,
		resolver:  resolver,
		content:   contentStore,
		fuseFS:    fuseFS,
		telemetry: telemetry,
	}, nil
}

// Stat returns the info for an active or committed snapshot by the key
func (s *Snapshotter) Stat(ctx context.Context, key string) (snapshots.Info, error) {
	ctx, t, err := s.ms.TransactionContext(ctx, false)
	if err != nil {
		return snapshots.Info{}, err
	}
	defer t.Rollback()

	_, info, _, err := storage.GetInfo(ctx, key)
	if err != nil {
		return snapshots.Info{}, err
	}

	return info, nil
}

// Update updates the info for a snapshot by the key
func (s *Snapshotter) Update(ctx context.Context, info snapshots.Info, fieldpaths ...string) (snapshots.Info, error) {
	ctx, t, err := s.ms.TransactionContext(ctx, true)
	if err != nil {
		return snapshots.Info{}, err
	}

	info, err = storage.UpdateInfo(ctx, info, fieldpaths...)
	if err != nil {
		t.Rollback()
		return snapshots.Info{}, err
	}

	if err := t.Commit(); err != nil {
		return snapshots.Info{}, err
	}

	return info, nil
}

// Usage returns the resource usage of an active or committed snapshot
func (s *Snapshotter) Usage(ctx context.Context, key string) (snapshots.Usage, error) {
	ctx, t, err := s.ms.TransactionContext(ctx, false)
	if err != nil {
		return snapshots.Usage{}, err
	}
	defer t.Rollback()

	id, info, usage, err := storage.GetInfo(ctx, key)
	if err != nil {
		return snapshots.Usage{}, err
	}

	if info.Kind == snapshots.KindActive {
		usage, err = s.calculateActiveUsage(ctx, id, usage)
		if err != nil {
			return snapshots.Usage{}, err
		}
	}

	return usage, nil
}

// Mounts returns the mounts for the active snapshot transaction identified by key
func (s *Snapshotter) Mounts(ctx context.Context, key string) ([]mount.Mount, error) {
	ctx, t, err := s.ms.TransactionContext(ctx, false)
	if err != nil {
		return nil, err
	}
	defer t.Rollback()

	snapshot, err := storage.GetSnapshot(ctx, key)
	if err != nil {
		return nil, err
	}

	return s.mounts(ctx, snapshot, key)
}

// Prepare creates an active snapshot identified by key descending from the provided parent
func (s *Snapshotter) Prepare(ctx context.Context, key, parent string, opts ...snapshots.Opt) ([]mount.Mount, error) {
	return s.createSnapshot(ctx, snapshots.KindActive, key, parent, opts...)
}

// View returns a readonly view of the snapshot identified by key
func (s *Snapshotter) View(ctx context.Context, key, parent string, opts ...snapshots.Opt) ([]mount.Mount, error) {
	return s.createSnapshot(ctx, snapshots.KindView, key, parent, opts...)
}

// Commit captures the changes between key and its parent into a snapshot identified by name
func (s *Snapshotter) Commit(ctx context.Context, name, key string, opts ...snapshots.Opt) error {
	ctx, t, err := s.ms.TransactionContext(ctx, true)
	if err != nil {
		return err
	}

	defer func() {
		if err != nil {
			if rerr := t.Rollback(); rerr != nil {
				log.G(ctx).WithError(rerr).Warn("failed to rollback transaction")
			}
		}
	}()

	// Check if target snapshot exists
	if _, err := storage.GetSnapshot(ctx, name); err == nil {
		return fmt.Errorf("snapshot %s: %w", name, errdefs.ErrAlreadyExists)
	}

	// Get the active snapshot
	active, err := storage.GetSnapshot(ctx, key)
	if err != nil {
		return err
	}

	if active.Kind != snapshots.KindActive {
		return fmt.Errorf("snapshot %s is not active: %w", key, errdefs.ErrInvalidArgument)
	}

	// Create the committed snapshot
	usage, err := s.calculateActiveUsage(ctx, active.ID, snapshots.Usage{})
	if err != nil {
		return err
	}

	if _, err := storage.CommitActive(ctx, key, name, usage, opts...); err != nil {
		return err
	}

	// Cleanup the active snapshot
	if err := s.cleanupActiveSnapshot(ctx, active); err != nil {
		log.G(ctx).WithError(err).Warn("failed to cleanup active snapshot")
	}

	return t.Commit()
}

// Remove removes the snapshot identified by key
func (s *Snapshotter) Remove(ctx context.Context, key string) error {
	ctx, t, err := s.ms.TransactionContext(ctx, true)
	if err != nil {
		return err
	}

	defer func() {
		if err != nil {
			if rerr := t.Rollback(); rerr != nil {
				log.G(ctx).WithError(rerr).Warn("failed to rollback transaction")
			}
		}
	}()

	// Get snapshot info
	id, info, err := storage.GetInfo(ctx, key)
	if err != nil {
		return err
	}

	// Remove from storage
	if err := storage.Remove(ctx, key); err != nil {
		return err
	}

	// Cleanup filesystem resources
	if err := s.cleanupSnapshot(ctx, id, info); err != nil {
		log.G(ctx).WithError(err).Warn("failed to cleanup snapshot")
	}

	return t.Commit()
}

// Walk calls the provided function for each snapshot
func (s *Snapshotter) Walk(ctx context.Context, fn snapshots.WalkFunc, filters ...string) error {
	ctx, t, err := s.ms.TransactionContext(ctx, false)
	if err != nil {
		return err
	}
	defer t.Rollback()

	return storage.WalkInfo(ctx, fn, filters...)
}

// Close closes the snapshotter
func (s *Snapshotter) Close() error {
	s.mu.Lock()
	defer s.mu.Unlock()

	if s.fuseFS != nil {
		if err := s.fuseFS.Close(); err != nil {
			log.L.WithError(err).Warn("failed to close FUSE filesystem")
		}
	}

	if s.ms != nil {
		return s.ms.Close()
	}

	return nil
}

// createSnapshot creates a new snapshot
func (s *Snapshotter) createSnapshot(ctx context.Context, kind snapshots.Kind, key, parent string, opts ...snapshots.Opt) ([]mount.Mount, error) {
	ctx, t, err := s.ms.TransactionContext(ctx, true)
	if err != nil {
		return nil, err
	}

	var base snapshots.Info
	for _, opt := range opts {
		if err := opt(&base); err != nil {
			t.Rollback()
			return nil, err
		}
	}

	var (
		target   []mount.Mount
		snapshot storage.Snapshot
	)

	if parent != "" {
		parentSnapshot, err := storage.GetSnapshot(ctx, parent)
		if err != nil {
			t.Rollback()
			return nil, err
		}

		snapshot = storage.Snapshot{
			Kind:      kind,
			ID:        identity.ChainID([]digest.Digest{parentSnapshot.ID, digest.FromString(key)}).String(),
			ParentIDs: []string{parentSnapshot.ID},
		}
	} else {
		snapshot = storage.Snapshot{
			Kind: kind,
			ID:   digest.FromString(key).String(),
		}
	}

	if _, err := storage.CreateSnapshot(ctx, kind, key, parent, opts...); err != nil {
		t.Rollback()
		return nil, err
	}

	// Create FUSE mount for the snapshot
	if kind == snapshots.KindActive || kind == snapshots.KindView {
		target, err = s.createFUSEMount(ctx, snapshot, key)
		if err != nil {
			t.Rollback()
			return nil, err
		}
	}

	if err := t.Commit(); err != nil {
		return nil, err
	}

	return target, nil
}

// createFUSEMount creates a FUSE mount for the snapshot
func (s *Snapshotter) createFUSEMount(ctx context.Context, snapshot storage.Snapshot, key string) ([]mount.Mount, error) {
	mountPoint := filepath.Join(s.root, "mounts", key)
	if err := os.MkdirAll(mountPoint, 0755); err != nil {
		return nil, fmt.Errorf("failed to create mount point: %w", err)
	}

	// Mount FUSE filesystem
	if err := s.fuseFS.Mount(ctx, mountPoint, snapshot); err != nil {
		return nil, fmt.Errorf("failed to mount FUSE filesystem: %w", err)
	}

	return []mount.Mount{
		{
			Type:    "bind",
			Source:  mountPoint,
			Options: []string{"rbind", "ro"},
		},
	}, nil
}

// mounts returns the mounts for a snapshot
func (s *Snapshotter) mounts(ctx context.Context, snapshot storage.Snapshot, key string) ([]mount.Mount, error) {
	if snapshot.Kind == snapshots.KindActive || snapshot.Kind == snapshots.KindView {
		return s.createFUSEMount(ctx, snapshot, key)
	}

	// For committed snapshots, create a view
	return s.createSnapshot(ctx, snapshots.KindView, key+"-view", key)
}

// calculateActiveUsage calculates usage for an active snapshot
func (s *Snapshotter) calculateActiveUsage(ctx context.Context, id string, usage snapshots.Usage) (snapshots.Usage, error) {
	// Implementation would calculate actual disk usage
	// For now, return the provided usage
	return usage, nil
}

// cleanupActiveSnapshot cleans up an active snapshot
func (s *Snapshotter) cleanupActiveSnapshot(ctx context.Context, snapshot storage.Snapshot) error {
	// Unmount FUSE filesystem if mounted
	mountPoint := filepath.Join(s.root, "mounts", snapshot.ID)
	if err := s.fuseFS.Unmount(ctx, mountPoint); err != nil {
		log.G(ctx).WithError(err).Warn("failed to unmount FUSE filesystem")
	}

	// Remove mount point directory
	if err := os.RemoveAll(mountPoint); err != nil {
		log.G(ctx).WithError(err).Warn("failed to remove mount point")
	}

	return nil
}

// cleanupSnapshot cleans up a snapshot
func (s *Snapshotter) cleanupSnapshot(ctx context.Context, id string, info snapshots.Info) error {
	// Cleanup any remaining FUSE mounts
	mountPoint := filepath.Join(s.root, "mounts", id)
	if err := s.fuseFS.Unmount(ctx, mountPoint); err != nil {
		log.G(ctx).WithError(err).Warn("failed to unmount FUSE filesystem")
	}

	// Remove mount point directory
	if err := os.RemoveAll(mountPoint); err != nil {
		log.G(ctx).WithError(err).Warn("failed to remove mount point")
	}

	return nil
}

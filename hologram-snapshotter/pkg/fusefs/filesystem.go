package fusefs

import (
	"context"
	"fmt"
	"os"
	"sync"
	"time"

	"bazil.org/fuse"
	"bazil.org/fuse/fs"
	"github.com/containerd/containerd/log"
	"github.com/containerd/containerd/snapshots/storage"

	"github.com/hologram/hologram-snapshotter/pkg/content"
)

// Filesystem represents a FUSE filesystem for serving OCI layers
type Filesystem struct {
	root      string
	content   *content.Store
	mounts    map[string]*Mount
	mu        sync.RWMutex
	telemetry *Telemetry
}

// Mount represents a mounted snapshot
type Mount struct {
	ID         string
	Snapshot   storage.Snapshot
	MountPoint string
	Conn       *fuse.Conn
	Server     *fs.Server
	Root       *Root
	Context    context.Context
	Cancel     context.CancelFunc
}

// Telemetry tracks filesystem metrics
type Telemetry struct {
	ReadOps     int64
	ReadBytes   int64
	ReadLatency time.Duration
	MountOps    int64
	UnmountOps  int64
}

// NewFilesystem creates a new FUSE filesystem
func NewFilesystem(root string, content *content.Store) (*Filesystem, error) {
	if err := os.MkdirAll(root, 0755); err != nil {
		return nil, fmt.Errorf("failed to create filesystem root: %w", err)
	}

	return &Filesystem{
		root:      root,
		content:   content,
		mounts:    make(map[string]*Mount),
		telemetry: &Telemetry{},
	}, nil
}

// Mount mounts a snapshot as a FUSE filesystem
func (f *Filesystem) Mount(ctx context.Context, mountPoint string, snapshot storage.Snapshot) error {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Check if already mounted
	if _, exists := f.mounts[snapshot.ID]; exists {
		return fmt.Errorf("snapshot %s already mounted", snapshot.ID)
	}

	// Create mount point directory
	if err := os.MkdirAll(mountPoint, 0755); err != nil {
		return fmt.Errorf("failed to create mount point: %w", err)
	}

	// Create FUSE connection
	conn, err := fuse.Mount(
		mountPoint,
		fuse.FSName("hologram"),
		fuse.Subtype("hologram-snapshotter"),
		fuse.LocalVolume(),
		fuse.VolumeName(fmt.Sprintf("hologram-%s", snapshot.ID)),
		fuse.ReadOnly(),
	)
	if err != nil {
		return fmt.Errorf("failed to mount FUSE: %w", err)
	}

	// Create context for this mount
	mountCtx, cancel := context.WithCancel(ctx)

	// Create root node
	root := &Root{
		fs:       f,
		snapshot: snapshot,
		content:  f.content,
		ctx:      mountCtx,
	}

	// Create FUSE server
	server := fs.New(conn, &fs.Config{
		Debug: func(msg interface{}) {
			log.G(mountCtx).Debugf("FUSE: %v", msg)
		},
	})

	// Start serving in background
	go func() {
		defer conn.Close()
		if err := server.Serve(root); err != nil {
			log.G(mountCtx).WithError(err).Error("FUSE server error")
		}
	}()

	// Wait for mount to be ready
	select {
	case <-conn.Ready:
		if err := conn.MountError; err != nil {
			cancel()
			return fmt.Errorf("FUSE mount error: %w", err)
		}
	case <-time.After(5 * time.Second):
		cancel()
		return fmt.Errorf("FUSE mount timeout")
	}

	// Store mount info
	f.mounts[snapshot.ID] = &Mount{
		ID:         snapshot.ID,
		Snapshot:   snapshot,
		MountPoint: mountPoint,
		Conn:       conn,
		Server:     server,
		Root:       root,
		Context:    mountCtx,
		Cancel:     cancel,
	}

	f.telemetry.MountOps++
	log.G(ctx).Infof("Mounted snapshot %s at %s", snapshot.ID, mountPoint)

	return nil
}

// Unmount unmounts a snapshot
func (f *Filesystem) Unmount(ctx context.Context, mountPoint string) error {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Find mount by mount point
	var mount *Mount
	for _, m := range f.mounts {
		if m.MountPoint == mountPoint {
			mount = m
			break
		}
	}

	if mount == nil {
		return fmt.Errorf("no mount found at %s", mountPoint)
	}

	// Cancel context
	mount.Cancel()

	// Unmount FUSE
	if err := fuse.Unmount(mountPoint); err != nil {
		log.G(ctx).WithError(err).Warn("failed to unmount FUSE")
	}

	// Close connection
	if err := mount.Conn.Close(); err != nil {
		log.G(ctx).WithError(err).Warn("failed to close FUSE connection")
	}

	// Remove from mounts
	delete(f.mounts, mount.ID)

	f.telemetry.UnmountOps++
	log.G(ctx).Infof("Unmounted snapshot %s from %s", mount.ID, mountPoint)

	return nil
}

// Close closes the filesystem
func (f *Filesystem) Close() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Unmount all mounts
	for _, mount := range f.mounts {
		mount.Cancel()
		if err := fuse.Unmount(mount.MountPoint); err != nil {
			log.L.WithError(err).Warnf("failed to unmount %s", mount.MountPoint)
		}
		if err := mount.Conn.Close(); err != nil {
			log.L.WithError(err).Warnf("failed to close connection for %s", mount.MountPoint)
		}
	}

	f.mounts = make(map[string]*Mount)
	return nil
}

// GetTelemetry returns filesystem telemetry
func (f *Filesystem) GetTelemetry() *Telemetry {
	f.mu.RLock()
	defer f.mu.RUnlock()
	return f.telemetry
}

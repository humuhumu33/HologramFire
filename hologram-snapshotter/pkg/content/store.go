package content

import (
	"context"
	"fmt"
	"io"
	"os"
	"sync"
	"time"

	"github.com/containerd/containerd"
	"github.com/containerd/containerd/content"
	"github.com/containerd/containerd/errdefs"
	"github.com/containerd/containerd/log"
	"github.com/containerd/containerd/snapshots/storage"
	"github.com/opencontainers/go-digest"
	ocispec "github.com/opencontainers/image-spec/specs-go/v1"
)

// Store wraps containerd's content store with hologram-specific functionality
type Store struct {
	client  *containerd.Client
	content content.Store
	root    string
	cache   map[string]*FileInfo
	mu      sync.RWMutex
}

// FileInfo represents file metadata
type FileInfo struct {
	Path    string
	Size    int64
	Mode    os.FileMode
	UID     uint32
	GID     uint32
	ModTime time.Time
	Digest  digest.Digest
}

// NewStore creates a new content store
func NewStore(client *containerd.Client, root string) (*Store, error) {
	if err := os.MkdirAll(root, 0755); err != nil {
		return nil, fmt.Errorf("failed to create content store root: %w", err)
	}

	return &Store{
		client:  client,
		content: client.ContentStore(),
		root:    root,
		cache:   make(map[string]*FileInfo),
	}, nil
}

// GetFileInfo returns file information for a given snapshot and path
func (s *Store) GetFileInfo(ctx context.Context, snapshotID, path string) (*FileInfo, error) {
	s.mu.RLock()
	cacheKey := fmt.Sprintf("%s:%s", snapshotID, path)
	if info, exists := s.cache[cacheKey]; exists {
		s.mu.RUnlock()
		return info, nil
	}
	s.mu.RUnlock()

	// For now, return mock file info
	// In a real implementation, this would read from the OCI layer manifest
	info := &FileInfo{
		Path:    path,
		Size:    1024, // Mock size
		Mode:    0444,
		UID:     0,
		GID:     0,
		ModTime: time.Now(),
		Digest:  digest.FromString(path),
	}

	// Cache the result
	s.mu.Lock()
	s.cache[cacheKey] = info
	s.mu.Unlock()

	return info, nil
}

// ReadFile reads file content from a snapshot
func (s *Store) ReadFile(ctx context.Context, snapshotID, path string, offset, size int64) ([]byte, error) {
	// For now, return mock content
	// In a real implementation, this would read from the actual OCI layer blob

	content := fmt.Sprintf("Mock content for %s in snapshot %s\n", path, snapshotID)

	// Handle offset and size
	if offset > int64(len(content)) {
		return []byte{}, nil
	}

	if size == 0 {
		size = int64(len(content))
	}

	end := offset + size
	if end > int64(len(content)) {
		end = int64(len(content))
	}

	return []byte(content[offset:end]), nil
}

// GetLayerManifest returns the manifest for a layer
func (s *Store) GetLayerManifest(ctx context.Context, snapshotID string) (*ocispec.Manifest, error) {
	// For now, return a mock manifest
	// In a real implementation, this would read from the content store
	return &ocispec.Manifest{
		Versioned: ocispec.Versioned{
			SchemaVersion: 2,
		},
		MediaType: ocispec.MediaTypeImageManifest,
		Config: ocispec.Descriptor{
			MediaType: ocispec.MediaTypeImageConfig,
			Digest:    digest.FromString("config-" + snapshotID),
			Size:      1024,
		},
		Layers: []ocispec.Descriptor{
			{
				MediaType: ocispec.MediaTypeImageLayer,
				Digest:    digest.FromString("layer-" + snapshotID),
				Size:      2048,
			},
		},
	}, nil
}

// GetLayerBlob returns a reader for a layer blob
func (s *Store) GetLayerBlob(ctx context.Context, digest digest.Digest) (io.ReadCloser, error) {
	reader, err := s.content.ReaderAt(ctx, ocispec.Descriptor{
		Digest: digest,
	})
	if err != nil {
		return nil, fmt.Errorf("failed to get layer blob: %w", err)
	}

	return &blobReader{
		reader: reader,
	}, nil
}

// blobReader wraps a content.ReaderAt as an io.ReadCloser
type blobReader struct {
	reader content.ReaderAt
	offset int64
}

func (r *blobReader) Read(p []byte) (n int, err error) {
	n, err = r.reader.ReadAt(p, r.offset)
	r.offset += int64(n)
	return n, err
}

func (r *blobReader) Close() error {
	return r.reader.Close()
}

// ResolveSnapshot resolves a snapshot to its layer digests
func (s *Store) ResolveSnapshot(ctx context.Context, snapshot storage.Snapshot) ([]digest.Digest, error) {
	var digests []digest.Digest

	// Add current layer
	digests = append(digests, digest.FromString(snapshot.ID))

	// Add parent layers
	for _, parentID := range snapshot.ParentIDs {
		digests = append(digests, digest.FromString(parentID))
	}

	return digests, nil
}

// GetSnapshotInfo returns information about a snapshot
func (s *Store) GetSnapshotInfo(ctx context.Context, snapshotID string) (*storage.Snapshot, error) {
	// This would typically query the snapshotter's metastore
	// For now, return a mock snapshot
	return &storage.Snapshot{
		ID:        snapshotID,
		Kind:      storage.KindCommitted,
		ParentIDs: []string{},
	}, nil
}

// PrefetchLayer prefetches a layer for better performance
func (s *Store) PrefetchLayer(ctx context.Context, digest digest.Digest) error {
	// Check if layer already exists
	_, err := s.content.Info(ctx, ocispec.Descriptor{
		Digest: digest,
	})
	if err == nil {
		return nil // Layer already exists
	}
	if !errdefs.IsNotFound(err) {
		return fmt.Errorf("failed to check layer existence: %w", err)
	}

	// In a real implementation, this would fetch the layer from a registry
	// For now, just log the prefetch request
	log.G(ctx).Infof("Prefetching layer %s", digest)

	return nil
}

// Cleanup removes cached data for a snapshot
func (s *Store) Cleanup(ctx context.Context, snapshotID string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	// Remove cached file info for this snapshot
	for key := range s.cache {
		if len(key) > len(snapshotID) && key[:len(snapshotID)] == snapshotID {
			delete(s.cache, key)
		}
	}

	return nil
}

// GetStats returns content store statistics
func (s *Store) GetStats() map[string]interface{} {
	s.mu.RLock()
	defer s.mu.RUnlock()

	return map[string]interface{}{
		"cached_files": len(s.cache),
		"root":         s.root,
	}
}

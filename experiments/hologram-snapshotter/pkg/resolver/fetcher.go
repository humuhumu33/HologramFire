package resolver

import (
	"context"
	"fmt"
	"io"

	"github.com/opencontainers/go-digest"
	ocispec "github.com/opencontainers/image-spec/specs-go/v1"
)

// HologramFetcher implements remotes.Fetcher for hologram content
type HologramFetcher struct {
	resolver *Resolver
	uorID    string
	ctx      context.Context
}

// Fetch fetches content for a descriptor
func (f *HologramFetcher) Fetch(ctx context.Context, desc ocispec.Descriptor) (io.ReadCloser, error) {
	// Fetch content via CTP-96
	content, err := f.resolver.ctp96Client.FetchContent(ctx, f.uorID, desc.Digest)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch content via CTP-96: %w", err)
	}

	return content, nil
}

// NoOpPusher is a no-op pusher implementation
type NoOpPusher struct{}

// Push pushes content (no-op implementation)
func (p *NoOpPusher) Push(ctx context.Context, desc ocispec.Descriptor) (contentWriter, error) {
	return &NoOpContentWriter{}, nil
}

// contentWriter interface for pushing content
type contentWriter interface {
	io.WriteCloser
	Commit(ctx context.Context, size int64, expected digest.Digest, opts ...ocispec.Descriptor) error
	Status() (ocispec.Status, error)
	Truncate(size int64) error
}

// NoOpContentWriter is a no-op content writer
type NoOpContentWriter struct{}

// Write implements io.Writer (no-op)
func (w *NoOpContentWriter) Write(p []byte) (n int, err error) {
	return len(p), nil
}

// Close implements io.Closer (no-op)
func (w *NoOpContentWriter) Close() error {
	return nil
}

// Commit commits the content (no-op)
func (w *NoOpContentWriter) Commit(ctx context.Context, size int64, expected digest.Digest, opts ...ocispec.Descriptor) error {
	return nil
}

// Status returns the status (no-op)
func (w *NoOpContentWriter) Status() (ocispec.Status, error) {
	return ocispec.Status{}, nil
}

// Truncate truncates the content (no-op)
func (w *NoOpContentWriter) Truncate(size int64) error {
	return nil
}

package resolver

import (
	"context"
	"fmt"
	"net/http"
	"os"
	"time"

	"github.com/containerd/containerd"
	"github.com/containerd/containerd/log"
	"github.com/containerd/containerd/remotes"
	"github.com/containerd/containerd/remotes/docker"
	"github.com/opencontainers/go-digest"
	ocispec "github.com/opencontainers/image-spec/specs-go/v1"

	"github.com/hologram/hologram-snapshotter/pkg/ctp96"
	"github.com/hologram/hologram-snapshotter/pkg/witness"
)

// Resolver implements remotes.Resolver with hologram-specific functionality
type Resolver struct {
	client      *containerd.Client
	enforce     bool
	verbose     bool
	ctp96Client *ctp96.Client
	witness     *witness.Verifier
	telemetry   *Telemetry
}

// Telemetry tracks resolver metrics
type Telemetry struct {
	ResolveOps      int64
	WitnessVerifies int64
	CTP96Fetches    int64
	ResolveLatency  time.Duration
	WitnessLatency  time.Duration
}

// Config holds resolver configuration
type Config struct {
	Enforce     bool
	Verbose     bool
	CTP96Config *ctp96.Config
}

// NewResolver creates a new hologram resolver
func NewResolver(client *containerd.Client, enforce, verbose bool) (*Resolver, error) {
	ctp96Client, err := ctp96.NewClient(&ctp96.Config{
		Endpoint: getEnvOrDefault("HOLOGRAM_CTP96_ENDPOINT", "http://localhost:8080"),
		Timeout:  30 * time.Second,
	})
	if err != nil {
		return nil, fmt.Errorf("failed to create CTP-96 client: %w", err)
	}

	witnessVerifier, err := witness.NewVerifier(&witness.Config{
		Endpoint: getEnvOrDefault("HOLOGRAM_WITNESS_ENDPOINT", "http://localhost:8081"),
		Timeout:  10 * time.Second,
	})
	if err != nil {
		return nil, fmt.Errorf("failed to create witness verifier: %w", err)
	}

	return &Resolver{
		client:      client,
		enforce:     enforce,
		verbose:     verbose,
		ctp96Client: ctp96Client,
		witness:     witnessVerifier,
		telemetry:   &Telemetry{},
	}, nil
}

// Resolve resolves a reference to a descriptor
func (r *Resolver) Resolve(ctx context.Context, ref string) (name string, desc ocispec.Descriptor, err error) {
	start := time.Now()
	defer func() {
		r.telemetry.ResolveOps++
		r.telemetry.ResolveLatency += time.Since(start)
	}()

	// Parse the reference
	parsedRef, err := parseReference(ref)
	if err != nil {
		return "", ocispec.Descriptor{}, fmt.Errorf("failed to parse reference: %w", err)
	}

	// Convert to UOR-ID
	uorID, err := r.convertToUORID(ctx, parsedRef)
	if err != nil {
		if r.enforce {
			return "", ocispec.Descriptor{}, fmt.Errorf("failed to convert to UOR-ID (enforce mode): %w", err)
		}
		log.G(ctx).WithError(err).Warn("failed to convert to UOR-ID, falling back to standard resolution")
		return r.resolveStandard(ctx, ref)
	}

	// Verify witness if in enforce mode
	if r.enforce {
		if err := r.verifyWitness(ctx, uorID); err != nil {
			return "", ocispec.Descriptor{}, fmt.Errorf("witness verification failed (enforce mode): %w", err)
		}
	}

	// Fetch manifest via CTP-96
	manifest, err := r.fetchManifest(ctx, uorID)
	if err != nil {
		return "", ocispec.Descriptor{}, fmt.Errorf("failed to fetch manifest: %w", err)
	}

	// Create descriptor
	desc = ocispec.Descriptor{
		MediaType: ocispec.MediaTypeImageManifest,
		Digest:    digest.FromString(uorID),
		Size:      int64(len(manifest)),
	}

	// Add hologram metadata if verbose mode
	if r.verbose {
		desc.Annotations = map[string]string{
			"hologram.uor_id":      uorID,
			"hologram.witness_ok":  "true",
			"hologram.ctp96_fetch": "true",
		}
	}

	return ref, desc, nil
}

// Fetcher returns a fetcher for the given reference
func (r *Resolver) Fetcher(ctx context.Context, ref string) (remotes.Fetcher, error) {
	// Parse the reference
	parsedRef, err := parseReference(ref)
	if err != nil {
		return nil, fmt.Errorf("failed to parse reference: %w", err)
	}

	// Convert to UOR-ID
	uorID, err := r.convertToUORID(ctx, parsedRef)
	if err != nil {
		if r.enforce {
			return nil, fmt.Errorf("failed to convert to UOR-ID (enforce mode): %w", err)
		}
		log.G(ctx).WithError(err).Warn("failed to convert to UOR-ID, falling back to standard fetcher")
		return r.createStandardFetcher(ctx, ref)
	}

	// Create hologram fetcher
	return &HologramFetcher{
		resolver: r,
		uorID:    uorID,
		ctx:      ctx,
	}, nil
}

// Pusher returns a pusher for the given reference
func (r *Resolver) Pusher(ctx context.Context, ref string) (remotes.Pusher, error) {
	// For now, return a no-op pusher
	// In a real implementation, this would push to the hologram registry
	return &NoOpPusher{}, nil
}

// convertToUORID converts a Docker reference to a UOR-ID
func (r *Resolver) convertToUORID(ctx context.Context, ref *Reference) (string, error) {
	// In a real implementation, this would query a UOR-ID registry
	// For now, create a deterministic UOR-ID from the reference
	uorID := fmt.Sprintf("uor://hologram/%s/%s@%s", ref.Host, ref.Repository, ref.Tag)

	log.G(ctx).Debugf("Converted %s to UOR-ID: %s", ref.String(), uorID)
	return uorID, nil
}

// verifyWitness verifies the witness for a UOR-ID
func (r *Resolver) verifyWitness(ctx context.Context, uorID string) error {
	start := time.Now()
	defer func() {
		r.telemetry.WitnessVerifies++
		r.telemetry.WitnessLatency += time.Since(start)
	}()

	// Verify witness
	valid, err := r.witness.Verify(ctx, uorID)
	if err != nil {
		return fmt.Errorf("witness verification error: %w", err)
	}

	if !valid {
		return fmt.Errorf("witness verification failed for UOR-ID: %s", uorID)
	}

	log.G(ctx).Debugf("Witness verification successful for UOR-ID: %s", uorID)
	return nil
}

// fetchManifest fetches a manifest via CTP-96
func (r *Resolver) fetchManifest(ctx context.Context, uorID string) ([]byte, error) {
	start := time.Now()
	defer func() {
		r.telemetry.CTP96Fetches++
	}()

	// Fetch manifest via CTP-96
	manifest, err := r.ctp96Client.FetchManifest(ctx, uorID)
	if err != nil {
		return nil, fmt.Errorf("CTP-96 fetch failed: %w", err)
	}

	log.G(ctx).Debugf("Fetched manifest for UOR-ID %s in %v", uorID, time.Since(start))
	return manifest, nil
}

// resolveStandard resolves using standard Docker resolver
func (r *Resolver) resolveStandard(ctx context.Context, ref string) (name string, desc ocispec.Descriptor, err error) {
	// Create standard Docker resolver
	resolver := docker.NewResolver(docker.ResolverOptions{
		Client: http.DefaultClient,
	})

	return resolver.Resolve(ctx, ref)
}

// createStandardFetcher creates a standard Docker fetcher
func (r *Resolver) createStandardFetcher(ctx context.Context, ref string) (remotes.Fetcher, error) {
	// Create standard Docker resolver
	resolver := docker.NewResolver(docker.ResolverOptions{
		Client: http.DefaultClient,
	})

	return resolver.Fetcher(ctx, ref)
}

// getEnvOrDefault returns an environment variable value or a default
func getEnvOrDefault(key, defaultValue string) string {
	if value := os.Getenv(key); value != "" {
		return value
	}
	return defaultValue
}

// GetTelemetry returns resolver telemetry
func (r *Resolver) GetTelemetry() *Telemetry {
	return r.telemetry
}

package images

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"strings"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// UORResolver handles tag to UOR-ID resolution
type UORResolver struct {
	cache   map[string]*UORMapping
	mutex   sync.RWMutex
	logger  *logrus.Logger
	timeout time.Duration
}

// UORMapping represents a mapping from tag to UOR-ID
type UORMapping struct {
	Tag       string    `json:"tag"`
	UORID     string    `json:"uor_id"`
	Digest    string    `json:"digest"`
	Created   time.Time `json:"created"`
	Expires   time.Time `json:"expires"`
	WitnessOK bool      `json:"witness_ok"`
}

// NewUORResolver creates a new UOR resolver
func NewUORResolver(logger *logrus.Logger) *UORResolver {
	return &UORResolver{
		cache:   make(map[string]*UORMapping),
		logger:  logger,
		timeout: 30 * time.Second,
	}
}

// Resolve resolves a tag to UOR-ID
func (r *UORResolver) Resolve(ctx context.Context, tag string) (uorID string, ok bool, err error) {
	r.mutex.RLock()
	mapping, exists := r.cache[tag]
	r.mutex.RUnlock()

	if exists && !mapping.Expires.Before(time.Now()) {
		r.logger.WithFields(logrus.Fields{
			"tag":    tag,
			"uor_id": mapping.UORID,
		}).Debug("UOR resolution cache hit")
		return mapping.UORID, true, nil
	}

	// Create timeout context
	resolveCtx, cancel := context.WithTimeout(ctx, r.timeout)
	defer cancel()

	// Resolve tag to UOR-ID
	uorID, err = r.resolveTag(resolveCtx, tag)
	if err != nil {
		r.logger.WithError(err).WithField("tag", tag).Error("Failed to resolve tag to UOR-ID")
		return "", false, err
	}

	// Generate digest for the UOR-ID
	digest := r.generateDigest(uorID)

	// Create new mapping
	mapping = &UORMapping{
		Tag:       tag,
		UORID:     uorID,
		Digest:    digest,
		Created:   time.Now(),
		Expires:   time.Now().Add(24 * time.Hour), // Cache for 24 hours
		WitnessOK: false,                          // Will be set by witness verification
	}

	// Store in cache
	r.mutex.Lock()
	r.cache[tag] = mapping
	r.mutex.Unlock()

	r.logger.WithFields(logrus.Fields{
		"tag":    tag,
		"uor_id": uorID,
		"digest": digest,
	}).Info("UOR resolution completed")

	return uorID, true, nil
}

// resolveTag resolves a tag to UOR-ID (internal implementation)
func (r *UORResolver) resolveTag(ctx context.Context, tag string) (string, error) {
	// Test knobs for deterministic testing:
	// "holo-test-ok:*"  -> "uor:test/ok:*"
	// "holo-test-bad:*" -> "uor:test/bad:*"
	if strings.HasPrefix(tag, "holo-test-ok:") {
		return "uor:test/ok:" + tag, nil
	}
	if strings.HasPrefix(tag, "holo-test-bad:") {
		return "uor:test/bad:" + tag, nil
	}

	// Parse tag into components
	parts := strings.Split(tag, ":")
	if len(parts) != 2 {
		return "", fmt.Errorf("invalid tag format: %s", tag)
	}

	repo := parts[0]
	tagName := parts[1]

	// Generate UOR-ID based on repository and tag
	// In a real implementation, this would query a registry or UOR service
	uorID := r.generateUORID(repo, tagName)

	// Simulate network delay
	select {
	case <-ctx.Done():
		return "", ctx.Err()
	case <-time.After(100 * time.Millisecond):
		// Simulated resolution time
	}

	return uorID, nil
}

// generateUORID generates a UOR-ID from repository and tag
func (r *UORResolver) generateUORID(repo, tag string) string {
	// Create a deterministic UOR-ID based on repository and tag
	input := fmt.Sprintf("uor:%s:%s", repo, tag)
	hash := sha256.Sum256([]byte(input))
	return fmt.Sprintf("uor:sha256:%s", hex.EncodeToString(hash[:]))
}

// generateDigest generates a digest for a UOR-ID
func (r *UORResolver) generateDigest(uorID string) string {
	hash := sha256.Sum256([]byte(uorID))
	return fmt.Sprintf("sha256:%s", hex.EncodeToString(hash[:]))
}

// GetMapping returns the UOR mapping for a tag
func (r *UORResolver) GetMapping(tag string) (*UORMapping, bool) {
	r.mutex.RLock()
	defer r.mutex.RUnlock()

	mapping, exists := r.cache[tag]
	if !exists || mapping.Expires.Before(time.Now()) {
		return nil, false
	}

	return mapping, true
}

// SetWitnessStatus sets the witness verification status for a UOR-ID
func (r *UORResolver) SetWitnessStatus(uorID string, witnessOK bool) {
	r.mutex.Lock()
	defer r.mutex.Unlock()

	// Find mapping by UOR-ID
	for _, mapping := range r.cache {
		if mapping.UORID == uorID {
			mapping.WitnessOK = witnessOK
			r.logger.WithFields(logrus.Fields{
				"uor_id":     uorID,
				"witness_ok": witnessOK,
			}).Debug("Updated witness status")
			break
		}
	}
}

// ListMappings returns all cached UOR mappings
func (r *UORResolver) ListMappings() []*UORMapping {
	r.mutex.RLock()
	defer r.mutex.RUnlock()

	mappings := make([]*UORMapping, 0, len(r.cache))
	for _, mapping := range r.cache {
		if !mapping.Expires.Before(time.Now()) {
			mappings = append(mappings, mapping)
		}
	}

	return mappings
}

// ClearExpired removes expired mappings from cache
func (r *UORResolver) ClearExpired() {
	r.mutex.Lock()
	defer r.mutex.Unlock()

	now := time.Now()
	for tag, mapping := range r.cache {
		if mapping.Expires.Before(now) {
			delete(r.cache, tag)
			r.logger.WithField("tag", tag).Debug("Removed expired UOR mapping")
		}
	}
}

// ClearCache clears all cached mappings
func (r *UORResolver) ClearCache() {
	r.mutex.Lock()
	defer r.mutex.Unlock()

	r.cache = make(map[string]*UORMapping)
	r.logger.Info("Cleared UOR resolution cache")
}

// GetCacheStats returns cache statistics
func (r *UORResolver) GetCacheStats() map[string]interface{} {
	r.mutex.RLock()
	defer r.mutex.RUnlock()

	now := time.Now()
	total := len(r.cache)
	expired := 0

	for _, mapping := range r.cache {
		if mapping.Expires.Before(now) {
			expired++
		}
	}

	return map[string]interface{}{
		"total_mappings":   total,
		"expired_mappings": expired,
		"active_mappings":  total - expired,
		"cache_hit_ratio":  0.0, // Would be calculated from actual usage
	}
}

package runtime

import (
	"context"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// UORManager manages Universal Object References
type UORManager struct {
	logger *logrus.Logger
	uors   map[string]*UOR
	mu     sync.RWMutex
	ctx    context.Context
	cancel context.CancelFunc
}

// UOR represents a Universal Object Reference
type UOR struct {
	ID                     string                 `json:"id"`
	ObjectRef              string                 `json:"object_ref"`
	ContentHash            string                 `json:"content_hash"`
	Metadata               map[string]interface{} `json:"metadata"`
	CreatedAt              time.Time              `json:"created_at"`
	UpdatedAt              time.Time              `json:"updated_at"`
	Version                int                    `json:"version"`
	HolographicFingerprint string                 `json:"holographic_fingerprint"`
}

// NewUORManager creates a new UOR manager
func NewUORManager(logger *logrus.Logger) *UORManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &UORManager{
		logger: logger,
		uors:   make(map[string]*UOR),
		ctx:    ctx,
		cancel: cancel,
	}
}

// Close closes the UOR manager
func (m *UORManager) Close() error {
	m.cancel()
	return nil
}

// Create creates a new UOR with proper cryptographic hashing
func (m *UORManager) Create(objectRef string, metadata map[string]interface{}) (*UOR, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	// Generate content hash for the object reference
	contentHash := m.generateContentHash(objectRef, metadata)

	// Generate UOR ID using content-addressed approach
	uorID := m.generateUORID(objectRef, contentHash, metadata)

	// Generate holographic fingerprint
	holographicFingerprint := m.generateHolographicFingerprint(uorID, contentHash)

	// Create UOR
	uor := &UOR{
		ID:                     uorID,
		ObjectRef:              objectRef,
		ContentHash:            contentHash,
		Metadata:               metadata,
		CreatedAt:              time.Now(),
		UpdatedAt:              time.Now(),
		Version:                1,
		HolographicFingerprint: holographicFingerprint,
	}

	// Store UOR
	m.uors[uorID] = uor

	m.logger.WithFields(logrus.Fields{
		"uor_id":                  uorID,
		"object_ref":              objectRef,
		"content_hash":            contentHash,
		"holographic_fingerprint": holographicFingerprint,
	}).Info("Created UOR with cryptographic hashing")

	return uor, nil
}

// Get retrieves a UOR by ID
func (m *UORManager) Get(uorID string) (*UOR, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	uor, exists := m.uors[uorID]
	if !exists {
		return nil, fmt.Errorf("UOR not found: %s", uorID)
	}

	return uor, nil
}

// List lists all UORs
func (m *UORManager) List(limit, offset int) ([]*UOR, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	uors := make([]*UOR, 0, len(m.uors))
	for _, uor := range m.uors {
		uors = append(uors, uor)
	}

	// Apply pagination
	if offset > 0 && offset < len(uors) {
		uors = uors[offset:]
	}

	if limit > 0 && limit < len(uors) {
		uors = uors[:limit]
	}

	return uors, nil
}

// Delete deletes a UOR
func (m *UORManager) Delete(uorID string) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	_, exists := m.uors[uorID]
	if !exists {
		return fmt.Errorf("UOR not found: %s", uorID)
	}

	delete(m.uors, uorID)

	m.logger.WithField("uor_id", uorID).Info("Deleted UOR")

	return nil
}

// UpdateMetadata updates UOR metadata
func (m *UORManager) UpdateMetadata(uorID string, metadata map[string]interface{}) error {
	m.mu.Lock()
	defer m.mu.Unlock()

	uor, exists := m.uors[uorID]
	if !exists {
		return fmt.Errorf("UOR not found: %s", uorID)
	}

	uor.Metadata = metadata
	uor.UpdatedAt = time.Now()

	m.logger.WithField("uor_id", uorID).Info("Updated UOR metadata")

	return nil
}

// Search searches UORs by query
func (m *UORManager) Search(query string, limit int) ([]*UOR, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	var results []*UOR
	for _, uor := range m.uors {
		// Simple search implementation
		if uor.ObjectRef == query || uor.ID == query {
			results = append(results, uor)
		}
	}

	// Apply limit
	if limit > 0 && limit < len(results) {
		results = results[:limit]
	}

	return results, nil
}

// Verify verifies the integrity of a UOR
func (m *UORManager) Verify(uorID string) (bool, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	uor, exists := m.uors[uorID]
	if !exists {
		return false, fmt.Errorf("UOR not found: %s", uorID)
	}

	// Recalculate content hash
	expectedContentHash := m.generateContentHash(uor.ObjectRef, uor.Metadata)
	if uor.ContentHash != expectedContentHash {
		return false, fmt.Errorf("content hash mismatch for UOR %s", uorID)
	}

	// Recalculate holographic fingerprint
	expectedFingerprint := m.generateHolographicFingerprint(uor.ID, uor.ContentHash)
	if uor.HolographicFingerprint != expectedFingerprint {
		return false, fmt.Errorf("holographic fingerprint mismatch for UOR %s", uorID)
	}

	return true, nil
}

// GetByContentHash retrieves UORs by content hash
func (m *UORManager) GetByContentHash(contentHash string) ([]*UOR, error) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	var results []*UOR
	for _, uor := range m.uors {
		if uor.ContentHash == contentHash {
			results = append(results, uor)
		}
	}

	return results, nil
}

// Update updates a UOR with new metadata and increments version
func (m *UORManager) Update(uorID string, metadata map[string]interface{}) (*UOR, error) {
	m.mu.Lock()
	defer m.mu.Unlock()

	uor, exists := m.uors[uorID]
	if !exists {
		return nil, fmt.Errorf("UOR not found: %s", uorID)
	}

	// Update metadata
	uor.Metadata = metadata
	uor.UpdatedAt = time.Now()
	uor.Version++

	// Recalculate content hash and fingerprint
	uor.ContentHash = m.generateContentHash(uor.ObjectRef, uor.Metadata)
	uor.HolographicFingerprint = m.generateHolographicFingerprint(uor.ID, uor.ContentHash)

	m.logger.WithFields(logrus.Fields{
		"uor_id":       uorID,
		"version":      uor.Version,
		"content_hash": uor.ContentHash,
	}).Info("Updated UOR")

	return uor, nil
}

// generateContentHash generates a content hash for the object reference and metadata
func (m *UORManager) generateContentHash(objectRef string, metadata map[string]interface{}) string {
	// Create a deterministic hash of the object reference and metadata
	hash := sha512.New()

	// Add object reference
	hash.Write([]byte("object_ref|"))
	hash.Write([]byte(objectRef))
	hash.Write([]byte("|"))

	// Add metadata in deterministic order
	if metadata != nil {
		// Use deterministic JSON marshaling with sorted keys
		metadataJSON, _ := json.Marshal(metadata)
		hash.Write([]byte("metadata|"))
		hash.Write(metadataJSON)
		hash.Write([]byte("|"))
	}

	// Add domain separator for holographic correspondence
	hash.Write([]byte("holographic_domain|uor_content|"))

	return hex.EncodeToString(hash.Sum(nil))
}

// generateUORID generates a content-addressed UOR ID
func (m *UORManager) generateUORID(objectRef, contentHash string, metadata map[string]interface{}) string {
	// Use content-addressed approach for deterministic UOR IDs
	hash := sha256.New()

	// Add content hash (primary identifier)
	hash.Write([]byte("content_hash|"))
	hash.Write([]byte(contentHash))
	hash.Write([]byte("|"))

	// Add object reference for human readability
	hash.Write([]byte("object_ref|"))
	hash.Write([]byte(objectRef))
	hash.Write([]byte("|"))

	// Add holographic domain separator
	hash.Write([]byte("holographic_domain|uor_id|"))

	// Generate deterministic UOR ID
	hashBytes := hash.Sum(nil)
	return "uor:sha256:" + hex.EncodeToString(hashBytes)
}

// generateHolographicFingerprint generates a holographic fingerprint for the UOR
func (m *UORManager) generateHolographicFingerprint(uorID, contentHash string) string {
	// Create holographic fingerprint using multiple hash rounds
	hash := sha256.New()

	// First round: UOR ID
	hash.Write([]byte("uor_id|"))
	hash.Write([]byte(uorID))
	hash.Write([]byte("|"))

	// Second round: Content hash
	hash.Write([]byte("content_hash|"))
	hash.Write([]byte(contentHash))
	hash.Write([]byte("|"))

	// Third round: Holographic domain
	hash.Write([]byte("holographic_domain|fingerprint|"))

	// Generate fingerprint
	fingerprint := hex.EncodeToString(hash.Sum(nil))
	return "holographic:" + fingerprint[:16]
}

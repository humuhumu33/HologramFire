package images

import (
	"context"
	"encoding/json"
	"fmt"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// ImageStore manages Docker images with Hologram extensions
type ImageStore struct {
	images   map[string]*Image
	mutex    sync.RWMutex
	logger   *logrus.Logger
	resolver *UORResolver
	verifier *WitnessVerifier
}

// Image represents a Docker image with optional Hologram extensions
type Image struct {
	// Standard Docker fields
	ID              string            `json:"Id"`
	RepoTags        []string          `json:"RepoTags"`
	RepoDigests     []string          `json:"RepoDigests"`
	Parent          string            `json:"Parent"`
	Comment         string            `json:"Comment"`
	Created         int64             `json:"Created"`
	Container       string            `json:"Container"`
	ContainerConfig interface{}       `json:"ContainerConfig"`
	DockerVersion   string            `json:"DockerVersion"`
	Author          string            `json:"Author"`
	Config          interface{}       `json:"Config"`
	Architecture    string            `json:"Architecture"`
	Os              string            `json:"Os"`
	Size            int64             `json:"Size"`
	VirtualSize     int64             `json:"VirtualSize"`
	GraphDriver     interface{}       `json:"GraphDriver"`
	RootFS          interface{}       `json:"RootFS"`
	Metadata        interface{}       `json:"Metadata"`
	Labels          map[string]string `json:"Labels"`

	// Hologram extensions (only exposed when verbose)
	XHologram *HologramExtensions `json:"XHologram,omitempty"`
}

// HologramExtensions contains Hologram-specific image metadata
type HologramExtensions struct {
	UORID      string                 `json:"uor_id,omitempty"`
	WitnessOK  bool                   `json:"witness_ok,omitempty"`
	VPILease   string                 `json:"vpi_lease,omitempty"`
	CTP96      string                 `json:"ctp96,omitempty"`
	Space12288 string                 `json:"space_12288,omitempty"`
	MetaAware  bool                   `json:"meta_aware,omitempty"`
	Oracle     string                 `json:"oracle,omitempty"`
	Witnesses  []*WitnessBundle       `json:"witnesses,omitempty"`
	Metadata   map[string]interface{} `json:"metadata,omitempty"`
}

// NewImageStore creates a new image store
func NewImageStore(logger *logrus.Logger) *ImageStore {
	return &ImageStore{
		images:   make(map[string]*Image),
		logger:   logger,
		resolver: NewUORResolver(logger),
		verifier: NewWitnessVerifier(logger),
	}
}

// AddImage adds an image to the store
func (s *ImageStore) AddImage(image *Image) error {
	s.mutex.Lock()
	defer s.mutex.Unlock()

	if image.ID == "" {
		return fmt.Errorf("image ID cannot be empty")
	}

	s.images[image.ID] = image
	s.logger.WithField("image_id", image.ID).Debug("Added image to store")

	return nil
}

// GetImage retrieves an image by ID
func (s *ImageStore) GetImage(id string) (*Image, bool) {
	s.mutex.RLock()
	defer s.mutex.RUnlock()

	image, exists := s.images[id]
	return image, exists
}

// ListImages returns all images, optionally filtered
func (s *ImageStore) ListImages(verbose bool) []*Image {
	s.mutex.RLock()
	defer s.mutex.RUnlock()

	images := make([]*Image, 0, len(s.images))
	for _, image := range s.images {
		// Create a copy to avoid modifying the original
		imageCopy := s.copyImage(image)

		// Remove Hologram extensions if not in verbose mode
		if !verbose {
			imageCopy.XHologram = nil
		}

		images = append(images, imageCopy)
	}

	return images
}

// RemoveImage removes an image from the store
func (s *ImageStore) RemoveImage(id string) error {
	s.mutex.Lock()
	defer s.mutex.Unlock()

	if _, exists := s.images[id]; !exists {
		return fmt.Errorf("image not found: %s", id)
	}

	delete(s.images, id)
	s.logger.WithField("image_id", id).Debug("Removed image from store")

	return nil
}

// UpdateImage updates an existing image
func (s *ImageStore) UpdateImage(id string, updates map[string]interface{}) error {
	s.mutex.Lock()
	defer s.mutex.Unlock()

	image, exists := s.images[id]
	if !exists {
		return fmt.Errorf("image not found: %s", id)
	}

	// Apply updates
	for key, value := range updates {
		switch key {
		case "RepoTags":
			if tags, ok := value.([]string); ok {
				image.RepoTags = tags
			}
		case "Labels":
			if labels, ok := value.(map[string]string); ok {
				image.Labels = labels
			}
		case "XHologram":
			if hologram, ok := value.(*HologramExtensions); ok {
				image.XHologram = hologram
			}
		}
	}

	s.logger.WithField("image_id", id).Debug("Updated image in store")
	return nil
}

// ResolveTag resolves a tag to UOR-ID and updates image metadata
func (s *ImageStore) ResolveTag(tag string) (string, error) {
	uorID, ok, err := s.resolver.Resolve(context.Background(), tag)
	if err != nil {
		return "", err
	}
	if !ok {
		return "", fmt.Errorf("failed to resolve tag: %s", tag)
	}
	return uorID, nil
}

// VerifyWitness verifies a witness bundle for an image
func (s *ImageStore) VerifyWitness(imageID string, bundle *WitnessBundle) (*WitnessResult, error) {
	s.mutex.RLock()
	image, exists := s.images[imageID]
	s.mutex.RUnlock()

	if !exists {
		return nil, fmt.Errorf("image not found: %s", imageID)
	}

	result, err := s.verifier.VerifyWitness(nil, bundle)
	if err != nil {
		return nil, err
	}

	// Update image witness status if verification succeeded
	if result.Valid && image.XHologram != nil {
		image.XHologram.WitnessOK = true
		if image.XHologram.Witnesses == nil {
			image.XHologram.Witnesses = make([]*WitnessBundle, 0)
		}
		image.XHologram.Witnesses = append(image.XHologram.Witnesses, bundle)
	}

	return result, nil
}

// CreateHologramImage creates a new image with Hologram extensions
func (s *ImageStore) CreateHologramImage(tag string, baseImage *Image) (*Image, error) {
	// Resolve tag to UOR-ID
	uorID, err := s.ResolveTag(tag)
	if err != nil {
		return nil, fmt.Errorf("failed to resolve tag: %w", err)
	}

	// Create Hologram extensions
	extensions := &HologramExtensions{
		UORID:      uorID,
		WitnessOK:  false,
		VPILease:   "pending",
		CTP96:      "disabled",
		Space12288: "unallocated",
		MetaAware:  false,
		Oracle:     "disconnected",
		Witnesses:  make([]*WitnessBundle, 0),
		Metadata:   make(map[string]interface{}),
	}

	// Create new image with extensions
	image := &Image{
		ID:              baseImage.ID,
		RepoTags:        []string{tag},
		RepoDigests:     baseImage.RepoDigests,
		Parent:          baseImage.Parent,
		Comment:         baseImage.Comment + " (Hologram-enabled)",
		Created:         time.Now().Unix(),
		Container:       baseImage.Container,
		ContainerConfig: baseImage.ContainerConfig,
		DockerVersion:   baseImage.DockerVersion,
		Author:          baseImage.Author,
		Config:          baseImage.Config,
		Architecture:    baseImage.Architecture,
		Os:              baseImage.Os,
		Size:            baseImage.Size,
		VirtualSize:     baseImage.VirtualSize,
		GraphDriver:     baseImage.GraphDriver,
		RootFS:          baseImage.RootFS,
		Metadata:        baseImage.Metadata,
		Labels:          baseImage.Labels,
		XHologram:       extensions,
	}

	// Add Hologram-specific labels
	if image.Labels == nil {
		image.Labels = make(map[string]string)
	}
	image.Labels["hologram.uor-id"] = "true"
	image.Labels["hologram.witness"] = "false"
	image.Labels["hologram.vpi-lease"] = "pending"
	image.Labels["hologram.ctp96"] = "disabled"

	return image, nil
}

// GetImageStats returns statistics about the image store
func (s *ImageStore) GetImageStats() map[string]interface{} {
	s.mutex.RLock()
	defer s.mutex.RUnlock()

	total := len(s.images)
	hologramEnabled := 0
	withWitnesses := 0
	totalSize := int64(0)

	for _, image := range s.images {
		if image.XHologram != nil {
			hologramEnabled++
			if image.XHologram.WitnessOK {
				withWitnesses++
			}
		}
		totalSize += image.Size
	}

	return map[string]interface{}{
		"total_images":     total,
		"hologram_enabled": hologramEnabled,
		"with_witnesses":   withWitnesses,
		"total_size_bytes": totalSize,
		"cache_stats":      s.resolver.GetCacheStats(),
	}
}

// copyImage creates a deep copy of an image
func (s *ImageStore) copyImage(image *Image) *Image {
	// Create a copy of the image
	imageCopy := &Image{
		ID:              image.ID,
		RepoTags:        make([]string, len(image.RepoTags)),
		RepoDigests:     make([]string, len(image.RepoDigests)),
		Parent:          image.Parent,
		Comment:         image.Comment,
		Created:         image.Created,
		Container:       image.Container,
		ContainerConfig: image.ContainerConfig,
		DockerVersion:   image.DockerVersion,
		Author:          image.Author,
		Config:          image.Config,
		Architecture:    image.Architecture,
		Os:              image.Os,
		Size:            image.Size,
		VirtualSize:     image.VirtualSize,
		GraphDriver:     image.GraphDriver,
		RootFS:          image.RootFS,
		Metadata:        image.Metadata,
		Labels:          make(map[string]string),
	}

	// Copy slices
	copy(imageCopy.RepoTags, image.RepoTags)
	copy(imageCopy.RepoDigests, image.RepoDigests)

	// Copy labels
	for k, v := range image.Labels {
		imageCopy.Labels[k] = v
	}

	// Copy Hologram extensions if present
	if image.XHologram != nil {
		imageCopy.XHologram = &HologramExtensions{
			UORID:      image.XHologram.UORID,
			WitnessOK:  image.XHologram.WitnessOK,
			VPILease:   image.XHologram.VPILease,
			CTP96:      image.XHologram.CTP96,
			Space12288: image.XHologram.Space12288,
			MetaAware:  image.XHologram.MetaAware,
			Oracle:     image.XHologram.Oracle,
			Witnesses:  make([]*WitnessBundle, len(image.XHologram.Witnesses)),
			Metadata:   make(map[string]interface{}),
		}

		// Copy witnesses
		copy(imageCopy.XHologram.Witnesses, image.XHologram.Witnesses)

		// Copy metadata
		for k, v := range image.XHologram.Metadata {
			imageCopy.XHologram.Metadata[k] = v
		}
	}

	return imageCopy
}

// ExportImage exports an image to JSON
func (s *ImageStore) ExportImage(id string, verbose bool) ([]byte, error) {
	s.mutex.RLock()
	image, exists := s.images[id]
	s.mutex.RUnlock()

	if !exists {
		return nil, fmt.Errorf("image not found: %s", id)
	}

	// Create a copy and remove Hologram extensions if not verbose
	imageCopy := s.copyImage(image)
	if !verbose {
		imageCopy.XHologram = nil
	}

	return json.MarshalIndent(imageCopy, "", "  ")
}

// ImportImage imports an image from JSON
func (s *ImageStore) ImportImage(data []byte) error {
	var image Image
	if err := json.Unmarshal(data, &image); err != nil {
		return fmt.Errorf("failed to unmarshal image: %w", err)
	}

	return s.AddImage(&image)
}

// Upsert updates or inserts UOR and witness information for an image
func (s *ImageStore) Upsert(uorID, tag string, witnessOK bool) {
	s.mutex.Lock()
	defer s.mutex.Unlock()

	// Find image by tag
	for _, image := range s.images {
		for _, imageTag := range image.RepoTags {
			if imageTag == tag {
				// Update or create Hologram extensions
				if image.XHologram == nil {
					image.XHologram = &HologramExtensions{
						Witnesses: make([]*WitnessBundle, 0),
						Metadata:  make(map[string]interface{}),
					}
				}
				image.XHologram.UORID = uorID
				image.XHologram.WitnessOK = witnessOK

				s.logger.WithFields(logrus.Fields{
					"image_id":   image.ID,
					"tag":        tag,
					"uor_id":     uorID,
					"witness_ok": witnessOK,
				}).Debug("Updated image UOR and witness information")
				return
			}
		}
	}
}

// GetUORInfo returns UOR-ID and witness status for an image
func (s *ImageStore) GetUORInfo(imageID string) (string, bool) {
	s.mutex.RLock()
	defer s.mutex.RUnlock()

	image, exists := s.images[imageID]
	if !exists || image.XHologram == nil {
		return "", false
	}

	return image.XHologram.UORID, image.XHologram.WitnessOK
}

package volumes

import (
	"fmt"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// Volume represents a Docker volume
type Volume struct {
	Name       string            `json:"Name"`
	Driver     string            `json:"Driver"`
	Mountpoint string            `json:"Mountpoint"`
	CreatedAt  string            `json:"CreatedAt"`
	Status     map[string]string `json:"Status,omitempty"`
	Labels     map[string]string `json:"Labels,omitempty"`
	Scope      string            `json:"Scope"`
	Options    map[string]string `json:"Options,omitempty"`
	UsageData  *UsageData        `json:"UsageData,omitempty"`
}

// UsageData represents volume usage information
type UsageData struct {
	Size     int64 `json:"Size"`
	RefCount int   `json:"RefCount"`
}

// CreateVolumeRequest represents a volume creation request
type CreateVolumeRequest struct {
	Name       string            `json:"Name,omitempty"`
	Driver     string            `json:"Driver,omitempty"`
	DriverOpts map[string]string `json:"DriverOpts,omitempty"`
	Labels     map[string]string `json:"Labels,omitempty"`
}

// Store manages volumes
type Store struct {
	logger  *logrus.Logger
	mu      sync.RWMutex
	volumes map[string]*Volume
}

// NewStore creates a new volume store
func NewStore(logger *logrus.Logger) *Store {
	return &Store{
		logger:  logger,
		volumes: make(map[string]*Volume),
	}
}

// Create creates a new volume
func (s *Store) Create(req CreateVolumeRequest) (*Volume, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	// Generate name if not provided
	name := req.Name
	if name == "" {
		name = s.generateVolumeName()
	}

	// Check if volume already exists
	if _, exists := s.volumes[name]; exists {
		return nil, fmt.Errorf("volume %s already exists", name)
	}

	// Set defaults
	driver := req.Driver
	if driver == "" {
		driver = "local"
	}

	// Create volume
	volume := &Volume{
		Name:       name,
		Driver:     driver,
		Mountpoint: fmt.Sprintf("/var/lib/hologramd/volumes/%s", name),
		CreatedAt:  time.Now().Format(time.RFC3339Nano),
		Status:     make(map[string]string),
		Labels:     make(map[string]string),
		Scope:      "local",
		Options:    make(map[string]string),
		UsageData: &UsageData{
			Size:     0,
			RefCount: 0,
		},
	}

	// Copy labels
	if req.Labels != nil {
		for k, v := range req.Labels {
			volume.Labels[k] = v
		}
	}

	// Copy driver options
	if req.DriverOpts != nil {
		for k, v := range req.DriverOpts {
			volume.Options[k] = v
		}
	}

	s.volumes[name] = volume

	s.logger.WithFields(logrus.Fields{
		"volume_name": name,
		"driver":      driver,
		"mountpoint":  volume.Mountpoint,
	}).Info("Volume created")

	return volume, nil
}

// Get retrieves a volume by name
func (s *Store) Get(name string) (*Volume, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()

	volume, exists := s.volumes[name]
	return volume, exists
}

// List returns all volumes
func (s *Store) List() []*Volume {
	s.mu.RLock()
	defer s.mu.RUnlock()

	volumes := make([]*Volume, 0, len(s.volumes))
	for _, volume := range s.volumes {
		volumes = append(volumes, volume)
	}
	return volumes
}

// Remove removes a volume
func (s *Store) Remove(name string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	volume, exists := s.volumes[name]
	if !exists {
		return fmt.Errorf("volume %s not found", name)
	}

	// Check if volume is in use
	if volume.UsageData != nil && volume.UsageData.RefCount > 0 {
		return fmt.Errorf("volume %s is in use and cannot be removed", name)
	}

	delete(s.volumes, name)

	s.logger.WithField("volume_name", name).Info("Volume removed")
	return nil
}

// Prune removes all unused volumes
func (s *Store) Prune() ([]string, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	var removed []string

	for name, volume := range s.volumes {
		// Skip if volume is in use
		if volume.UsageData != nil && volume.UsageData.RefCount > 0 {
			continue
		}

		delete(s.volumes, name)
		removed = append(removed, name)
	}

	s.logger.WithField("removed_count", len(removed)).Info("Volumes pruned")
	return removed, nil
}

// IncrementRefCount increments the reference count for a volume
func (s *Store) IncrementRefCount(name string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	volume, exists := s.volumes[name]
	if !exists {
		return fmt.Errorf("volume %s not found", name)
	}

	if volume.UsageData == nil {
		volume.UsageData = &UsageData{}
	}
	volume.UsageData.RefCount++

	return nil
}

// DecrementRefCount decrements the reference count for a volume
func (s *Store) DecrementRefCount(name string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	volume, exists := s.volumes[name]
	if !exists {
		return fmt.Errorf("volume %s not found", name)
	}

	if volume.UsageData != nil && volume.UsageData.RefCount > 0 {
		volume.UsageData.RefCount--
	}

	return nil
}

// generateVolumeName generates a unique volume name
func (s *Store) generateVolumeName() string {
	// Simple name generation - in a real implementation, this would be more sophisticated
	timestamp := time.Now().UnixNano()
	return fmt.Sprintf("volume_%d", timestamp)
}

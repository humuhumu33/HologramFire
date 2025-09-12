package runtime

import (
	"context"

	"github.com/hologram/engine/internal/volumes"
	"github.com/sirupsen/logrus"
)

// VolumeManager manages volumes
type VolumeManager struct {
	logger *logrus.Logger
	ctx    context.Context
	cancel context.CancelFunc
	store  *volumes.Store
}

// NewVolumeManager creates a new volume manager
func NewVolumeManager(logger *logrus.Logger) *VolumeManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &VolumeManager{
		logger: logger,
		ctx:    ctx,
		cancel: cancel,
		store:  volumes.NewStore(logger),
	}
}

// Close closes the volume manager
func (m *VolumeManager) Close() error {
	m.cancel()
	return nil
}

// GetStore returns the volume store
func (m *VolumeManager) GetStore() *volumes.Store {
	return m.store
}

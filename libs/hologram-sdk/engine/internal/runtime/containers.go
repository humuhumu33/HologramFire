package runtime

import (
	"context"

	"github.com/sirupsen/logrus"
)

// ContainerManager manages containers
type ContainerManager struct {
	logger *logrus.Logger
	ctx    context.Context
	cancel context.CancelFunc
	store  *Store
}

// NewContainerManager creates a new container manager
func NewContainerManager(logger *logrus.Logger) *ContainerManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &ContainerManager{
		logger: logger,
		ctx:    ctx,
		cancel: cancel,
		store:  NewStore(),
	}
}

// Close closes the container manager
func (m *ContainerManager) Close() error {
	m.cancel()
	return nil
}

// GetStore returns the container state store
func (m *ContainerManager) GetStore() *Store {
	return m.store
}

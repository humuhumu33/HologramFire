package runtime

import (
	"context"

	"github.com/sirupsen/logrus"
)

// SpaceManager manages 12,288 space
type SpaceManager struct {
	logger *logrus.Logger
	ctx    context.Context
	cancel context.CancelFunc
}

// NewSpaceManager creates a new space manager
func NewSpaceManager(logger *logrus.Logger) *SpaceManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &SpaceManager{
		logger: logger,
		ctx:    ctx,
		cancel: cancel,
	}
}

// Close closes the space manager
func (m *SpaceManager) Close() error {
	m.cancel()
	return nil
}

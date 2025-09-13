package runtime

import (
	"context"

	"github.com/sirupsen/logrus"
)

// ImageManager manages images
type ImageManager struct {
	logger *logrus.Logger
	ctx    context.Context
	cancel context.CancelFunc
}

// NewImageManager creates a new image manager
func NewImageManager(logger *logrus.Logger) *ImageManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &ImageManager{
		logger: logger,
		ctx:    ctx,
		cancel: cancel,
	}
}

// Close closes the image manager
func (m *ImageManager) Close() error {
	m.cancel()
	return nil
}

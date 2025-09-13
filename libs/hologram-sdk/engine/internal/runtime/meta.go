package runtime

import (
	"context"

	"github.com/sirupsen/logrus"
)

// MetaManager manages meta-awareness
type MetaManager struct {
	logger *logrus.Logger
	ctx    context.Context
	cancel context.CancelFunc
}

// NewMetaManager creates a new meta manager
func NewMetaManager(logger *logrus.Logger) *MetaManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &MetaManager{
		logger: logger,
		ctx:    ctx,
		cancel: cancel,
	}
}

// Close closes the meta manager
func (m *MetaManager) Close() error {
	m.cancel()
	return nil
}

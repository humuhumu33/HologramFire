package runtime

import (
	"context"

	"github.com/sirupsen/logrus"
)

// OracleManager manages oracles
type OracleManager struct {
	logger *logrus.Logger
	ctx    context.Context
	cancel context.CancelFunc
}

// NewOracleManager creates a new oracle manager
func NewOracleManager(logger *logrus.Logger) *OracleManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &OracleManager{
		logger: logger,
		ctx:    ctx,
		cancel: cancel,
	}
}

// Close closes the oracle manager
func (m *OracleManager) Close() error {
	m.cancel()
	return nil
}

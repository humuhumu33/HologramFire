package runtime

import (
	"context"

	"github.com/hologram/engine/internal/networks"
	"github.com/sirupsen/logrus"
)

// NetworkManager manages networks
type NetworkManager struct {
	logger        *logrus.Logger
	ctx           context.Context
	cancel        context.CancelFunc
	store         *networks.Store
	bridgeManager *networks.BridgeManager
	ctp96Manager  *networks.CTP96Manager
}

// NewNetworkManager creates a new network manager
func NewNetworkManager(logger *logrus.Logger) *NetworkManager {
	ctx, cancel := context.WithCancel(context.Background())

	return &NetworkManager{
		logger:        logger,
		ctx:           ctx,
		cancel:        cancel,
		store:         networks.NewStore(logger),
		bridgeManager: networks.NewBridgeManager(logger),
		ctp96Manager:  networks.NewCTP96Manager(logger),
	}
}

// Close closes the network manager
func (m *NetworkManager) Close() error {
	m.cancel()
	return nil
}

// GetStore returns the network store
func (m *NetworkManager) GetStore() *networks.Store {
	return m.store
}

// GetBridgeManager returns the bridge manager
func (m *NetworkManager) GetBridgeManager() *networks.BridgeManager {
	return m.bridgeManager
}

// GetCTP96Manager returns the CTP-96 manager
func (m *NetworkManager) GetCTP96Manager() *networks.CTP96Manager {
	return m.ctp96Manager
}

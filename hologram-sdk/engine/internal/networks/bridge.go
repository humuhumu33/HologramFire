package networks

import (
	"fmt"
	"sync"

	"github.com/sirupsen/logrus"
)

// BridgeManager manages bridge networks
type BridgeManager struct {
	logger  *logrus.Logger
	mu      sync.RWMutex
	bridges map[string]*Bridge
}

// Bridge represents a bridge network
type Bridge struct {
	ID         string
	Name       string
	BridgeName string
	Subnet     string
	Gateway    string
	Containers map[string]*BridgeContainer
}

// BridgeContainer represents a container connected to a bridge
type BridgeContainer struct {
	ContainerID string
	EndpointID  string
	MacAddress  string
	IPAddress   string
	VethName    string
}

// NewBridgeManager creates a new bridge manager
func NewBridgeManager(logger *logrus.Logger) *BridgeManager {
	return &BridgeManager{
		logger:  logger,
		bridges: make(map[string]*Bridge),
	}
}

// CreateBridge creates a new bridge network
func (bm *BridgeManager) CreateBridge(networkID, name, subnet, gateway string) (*Bridge, error) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	// Check if bridge already exists
	if _, exists := bm.bridges[networkID]; exists {
		return nil, fmt.Errorf("bridge %s already exists", networkID)
	}

	// Generate bridge name
	bridgeName := fmt.Sprintf("br-%s", networkID[:8])

	bridge := &Bridge{
		ID:         networkID,
		Name:       name,
		BridgeName: bridgeName,
		Subnet:     subnet,
		Gateway:    gateway,
		Containers: make(map[string]*BridgeContainer),
	}

	bm.bridges[networkID] = bridge

	bm.logger.WithFields(logrus.Fields{
		"network_id":  networkID,
		"bridge_name": bridgeName,
		"subnet":      subnet,
		"gateway":     gateway,
	}).Info("Bridge network created")

	return bridge, nil
}

// GetBridge retrieves a bridge by ID
func (bm *BridgeManager) GetBridge(networkID string) (*Bridge, bool) {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	bridge, exists := bm.bridges[networkID]
	return bridge, exists
}

// RemoveBridge removes a bridge network
func (bm *BridgeManager) RemoveBridge(networkID string) error {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	bridge, exists := bm.bridges[networkID]
	if !exists {
		return fmt.Errorf("bridge %s not found", networkID)
	}

	// Check if bridge has connected containers
	if len(bridge.Containers) > 0 {
		return fmt.Errorf("bridge %s has connected containers and cannot be removed", networkID)
	}

	delete(bm.bridges, networkID)

	bm.logger.WithFields(logrus.Fields{
		"network_id":  networkID,
		"bridge_name": bridge.BridgeName,
	}).Info("Bridge network removed")

	return nil
}

// ConnectContainer connects a container to a bridge
func (bm *BridgeManager) ConnectContainer(networkID, containerID, endpointID string) (*BridgeContainer, error) {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	bridge, exists := bm.bridges[networkID]
	if !exists {
		return nil, fmt.Errorf("bridge %s not found", networkID)
	}

	// Check if container is already connected
	if _, exists := bridge.Containers[containerID]; exists {
		return nil, fmt.Errorf("container %s already connected to bridge %s", containerID, networkID)
	}

	// Generate MAC address and IP address
	macAddress := bm.generateMacAddress(containerID)
	ipAddress := bm.generateIPAddress(bridge, containerID)
	vethName := fmt.Sprintf("veth%s", containerID[:8])

	container := &BridgeContainer{
		ContainerID: containerID,
		EndpointID:  endpointID,
		MacAddress:  macAddress,
		IPAddress:   ipAddress,
		VethName:    vethName,
	}

	bridge.Containers[containerID] = container

	bm.logger.WithFields(logrus.Fields{
		"network_id":   networkID,
		"container_id": containerID,
		"endpoint_id":  endpointID,
		"ip_address":   ipAddress,
		"mac_address":  macAddress,
		"veth_name":    vethName,
	}).Info("Container connected to bridge")

	return container, nil
}

// DisconnectContainer disconnects a container from a bridge
func (bm *BridgeManager) DisconnectContainer(networkID, containerID string) error {
	bm.mu.Lock()
	defer bm.mu.Unlock()

	bridge, exists := bm.bridges[networkID]
	if !exists {
		return fmt.Errorf("bridge %s not found", networkID)
	}

	container, exists := bridge.Containers[containerID]
	if !exists {
		return fmt.Errorf("container %s not connected to bridge %s", containerID, networkID)
	}

	delete(bridge.Containers, containerID)

	bm.logger.WithFields(logrus.Fields{
		"network_id":   networkID,
		"container_id": containerID,
		"endpoint_id":  container.EndpointID,
	}).Info("Container disconnected from bridge")

	return nil
}

// GetContainer returns a container connected to a bridge
func (bm *BridgeManager) GetContainer(networkID, containerID string) (*BridgeContainer, bool) {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	bridge, exists := bm.bridges[networkID]
	if !exists {
		return nil, false
	}

	container, exists := bridge.Containers[containerID]
	return container, exists
}

// ListBridges returns all bridges
func (bm *BridgeManager) ListBridges() []*Bridge {
	bm.mu.RLock()
	defer bm.mu.RUnlock()

	bridges := make([]*Bridge, 0, len(bm.bridges))
	for _, bridge := range bm.bridges {
		bridges = append(bridges, bridge)
	}
	return bridges
}

// generateMacAddress generates a MAC address for a container
func (bm *BridgeManager) generateMacAddress(containerID string) string {
	// Generate a deterministic MAC address based on container ID
	// This is a simplified implementation
	hash := 0
	for _, c := range containerID {
		hash = hash*31 + int(c)
	}

	// Ensure it's a valid MAC address format
	return fmt.Sprintf("02:42:ac:11:%02x:%02x", (hash>>8)&0xff, hash&0xff)
}

// generateIPAddress generates an IP address for a container
func (bm *BridgeManager) generateIPAddress(bridge *Bridge, containerID string) string {
	// Generate a deterministic IP address based on container ID
	// This is a simplified implementation
	hash := 0
	for _, c := range containerID {
		hash = hash*31 + int(c)
	}

	// Generate IP in the subnet range (avoiding gateway)
	ip := (hash % 253) + 2 // 2-254 range, avoiding 1 (gateway)
	return fmt.Sprintf("172.17.0.%d", ip)
}

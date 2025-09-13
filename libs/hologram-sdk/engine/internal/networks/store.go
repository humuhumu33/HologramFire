package networks

import (
	"fmt"
	"sync"
	"time"

	"github.com/sirupsen/logrus"
)

// Network represents a Docker network
type Network struct {
	ID         string                `json:"Id"`
	Name       string                `json:"Name"`
	Created    string                `json:"Created"`
	Scope      string                `json:"Scope"`
	Driver     string                `json:"Driver"`
	EnableIPv6 bool                  `json:"EnableIPv6"`
	IPAM       *IPAM                 `json:"IPAM"`
	Internal   bool                  `json:"Internal"`
	Attachable bool                  `json:"Attachable"`
	Ingress    bool                  `json:"Ingress"`
	ConfigFrom map[string]string     `json:"ConfigFrom,omitempty"`
	ConfigOnly bool                  `json:"ConfigOnly"`
	Containers map[string]*Container `json:"Containers"`
	Options    map[string]string     `json:"Options"`
	Labels     map[string]string     `json:"Labels"`
	XHologram  map[string]any        `json:"XHologram,omitempty"` // Hologram-specific data
}

// IPAM represents IP Address Management configuration
type IPAM struct {
	Driver  string            `json:"Driver"`
	Options map[string]string `json:"Options,omitempty"`
	Config  []IPAMConfig      `json:"Config,omitempty"`
}

// IPAMConfig represents IPAM configuration
type IPAMConfig struct {
	Subnet  string `json:"Subnet,omitempty"`
	IPRange string `json:"IPRange,omitempty"`
	Gateway string `json:"Gateway,omitempty"`
}

// Container represents a container connected to a network
type Container struct {
	Name        string `json:"Name"`
	EndpointID  string `json:"EndpointID"`
	MacAddress  string `json:"MacAddress"`
	IPv4Address string `json:"IPv4Address"`
	IPv6Address string `json:"IPv6Address"`
}

// CreateNetworkRequest represents a network creation request
type CreateNetworkRequest struct {
	Name       string            `json:"Name"`
	Driver     string            `json:"Driver,omitempty"`
	EnableIPv6 bool              `json:"EnableIPv6,omitempty"`
	IPAM       *IPAM             `json:"IPAM,omitempty"`
	Internal   bool              `json:"Internal,omitempty"`
	Attachable bool              `json:"Attachable,omitempty"`
	Ingress    bool              `json:"Ingress,omitempty"`
	Options    map[string]string `json:"Options,omitempty"`
	Labels     map[string]string `json:"Labels,omitempty"`
}

// Store manages networks
type Store struct {
	logger   *logrus.Logger
	mu       sync.RWMutex
	networks map[string]*Network
	nextID   int
}

// NewStore creates a new network store
func NewStore(logger *logrus.Logger) *Store {
	return &Store{
		logger:   logger,
		networks: make(map[string]*Network),
	}
}

// Create creates a new network
func (s *Store) Create(req CreateNetworkRequest) (*Network, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	// Generate ID if not provided
	s.nextID++
	networkID := fmt.Sprintf("network_%d", s.nextID)

	// Check if network name already exists
	for _, network := range s.networks {
		if network.Name == req.Name {
			return nil, fmt.Errorf("network %s already exists", req.Name)
		}
	}

	// Set defaults
	driver := req.Driver
	if driver == "" {
		driver = "bridge"
	}

	// Create IPAM configuration if not provided
	ipam := req.IPAM
	if ipam == nil {
		ipam = &IPAM{
			Driver: "default",
			Config: []IPAMConfig{
				{
					Subnet:  "172.17.0.0/16",
					Gateway: "172.17.0.1",
				},
			},
		}
	}

	// Create network
	network := &Network{
		ID:         networkID,
		Name:       req.Name,
		Created:    time.Now().Format(time.RFC3339Nano),
		Scope:      "local",
		Driver:     driver,
		EnableIPv6: req.EnableIPv6,
		IPAM:       ipam,
		Internal:   req.Internal,
		Attachable: req.Attachable,
		Ingress:    req.Ingress,
		Containers: make(map[string]*Container),
		Options:    make(map[string]string),
		Labels:     make(map[string]string),
	}

	// Copy options
	if req.Options != nil {
		for k, v := range req.Options {
			network.Options[k] = v
		}
	}

	// Copy labels
	if req.Labels != nil {
		for k, v := range req.Labels {
			network.Labels[k] = v
		}
	}

	s.networks[networkID] = network

	s.logger.WithFields(logrus.Fields{
		"network_id": networkID,
		"name":       req.Name,
		"driver":     driver,
	}).Info("Network created")

	return network, nil
}

// Get retrieves a network by ID or name
func (s *Store) Get(idOrName string) (*Network, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()

	// Try by ID first
	if network, exists := s.networks[idOrName]; exists {
		return network, true
	}

	// Try by name
	for _, network := range s.networks {
		if network.Name == idOrName {
			return network, true
		}
	}

	return nil, false
}

// List returns all networks
func (s *Store) List() []*Network {
	s.mu.RLock()
	defer s.mu.RUnlock()

	networks := make([]*Network, 0, len(s.networks))
	for _, network := range s.networks {
		networks = append(networks, network)
	}
	return networks
}

// Remove removes a network
func (s *Store) Remove(idOrName string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	network, exists := s.networks[idOrName]
	if !exists {
		// Try by name
		for id, n := range s.networks {
			if n.Name == idOrName {
				network = n
				idOrName = id
				exists = true
				break
			}
		}
	}

	if !exists {
		return fmt.Errorf("network %s not found", idOrName)
	}

	// Check if network has connected containers
	if len(network.Containers) > 0 {
		return fmt.Errorf("network %s has connected containers and cannot be removed", network.Name)
	}

	delete(s.networks, idOrName)

	s.logger.WithFields(logrus.Fields{
		"network_id": idOrName,
		"name":       network.Name,
	}).Info("Network removed")

	return nil
}

// Connect connects a container to a network
func (s *Store) Connect(networkID, containerID string, containerName string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	network, exists := s.networks[networkID]
	if !exists {
		return fmt.Errorf("network %s not found", networkID)
	}

	// Generate endpoint ID
	endpointID := fmt.Sprintf("endpoint_%s_%s", networkID, containerID)

	// Create container entry
	container := &Container{
		Name:        containerName,
		EndpointID:  endpointID,
		MacAddress:  s.generateMacAddress(),
		IPv4Address: s.generateIPv4Address(network),
		IPv6Address: "",
	}

	network.Containers[containerID] = container

	s.logger.WithFields(logrus.Fields{
		"network_id":   networkID,
		"container_id": containerID,
		"endpoint_id":  endpointID,
	}).Info("Container connected to network")

	return nil
}

// Disconnect disconnects a container from a network
func (s *Store) Disconnect(networkID, containerID string) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	network, exists := s.networks[networkID]
	if !exists {
		return fmt.Errorf("network %s not found", networkID)
	}

	if _, exists := network.Containers[containerID]; !exists {
		return fmt.Errorf("container %s not connected to network %s", containerID, networkID)
	}

	delete(network.Containers, containerID)

	s.logger.WithFields(logrus.Fields{
		"network_id":   networkID,
		"container_id": containerID,
	}).Info("Container disconnected from network")

	return nil
}

// generateMacAddress generates a MAC address for a container
func (s *Store) generateMacAddress() string {
	// Simple MAC address generation
	return fmt.Sprintf("02:42:ac:11:%02x:%02x", s.nextID%256, (s.nextID/256)%256)
}

// generateIPv4Address generates an IPv4 address for a container
func (s *Store) generateIPv4Address(network *Network) string {
	// Simple IP address generation based on network subnet
	// This is a simplified implementation
	containerCount := len(network.Containers)
	return fmt.Sprintf("172.17.0.%d", containerCount+2)
}

// AddHologramData adds Hologram-specific data to a network
func (s *Store) AddHologramData(networkID string, data map[string]any) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	network, exists := s.networks[networkID]
	if !exists {
		return fmt.Errorf("network %s not found", networkID)
	}

	if network.XHologram == nil {
		network.XHologram = make(map[string]any)
	}

	for k, v := range data {
		network.XHologram[k] = v
	}

	return nil
}

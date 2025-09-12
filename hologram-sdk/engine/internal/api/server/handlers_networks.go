package server

import (
	"encoding/json"
	"fmt"
	"net/http"

	"github.com/gorilla/mux"
	"github.com/hologram/engine/internal/api"
	"github.com/hologram/engine/internal/events"
	"github.com/hologram/engine/internal/networks"
)

// NetworkCreateRequest represents a network creation request
type NetworkCreateRequest struct {
	Name       string            `json:"Name"`
	Driver     string            `json:"Driver,omitempty"`
	EnableIPv6 bool              `json:"EnableIPv6,omitempty"`
	IPAM       *networks.IPAM    `json:"IPAM,omitempty"`
	Internal   bool              `json:"Internal,omitempty"`
	Attachable bool              `json:"Attachable,omitempty"`
	Ingress    bool              `json:"Ingress,omitempty"`
	Options    map[string]string `json:"Options,omitempty"`
	Labels     map[string]string `json:"Labels,omitempty"`
}

// NetworkCreateResponse represents a network creation response
type NetworkCreateResponse struct {
	ID         string                         `json:"Id"`
	Name       string                         `json:"Name"`
	Created    string                         `json:"Created"`
	Scope      string                         `json:"Scope"`
	Driver     string                         `json:"Driver"`
	EnableIPv6 bool                           `json:"EnableIPv6"`
	IPAM       *networks.IPAM                 `json:"IPAM"`
	Internal   bool                           `json:"Internal"`
	Attachable bool                           `json:"Attachable"`
	Ingress    bool                           `json:"Ingress"`
	ConfigFrom map[string]string              `json:"ConfigFrom,omitempty"`
	ConfigOnly bool                           `json:"ConfigOnly"`
	Containers map[string]*networks.Container `json:"Containers"`
	Options    map[string]string              `json:"Options"`
	Labels     map[string]string              `json:"Labels"`
	XHologram  map[string]any                 `json:"XHologram,omitempty"`
}

// NetworkListResponse represents a network list response
type NetworkListResponse []*networks.Network

// NetworkInspectResponse represents a network inspect response
type NetworkInspectResponse struct {
	ID         string                         `json:"Id"`
	Name       string                         `json:"Name"`
	Created    string                         `json:"Created"`
	Scope      string                         `json:"Scope"`
	Driver     string                         `json:"Driver"`
	EnableIPv6 bool                           `json:"EnableIPv6"`
	IPAM       *networks.IPAM                 `json:"IPAM"`
	Internal   bool                           `json:"Internal"`
	Attachable bool                           `json:"Attachable"`
	Ingress    bool                           `json:"Ingress"`
	ConfigFrom map[string]string              `json:"ConfigFrom,omitempty"`
	ConfigOnly bool                           `json:"ConfigOnly"`
	Containers map[string]*networks.Container `json:"Containers"`
	Options    map[string]string              `json:"Options"`
	Labels     map[string]string              `json:"Labels"`
	XHologram  map[string]any                 `json:"XHologram,omitempty"`
}

// NetworkConnectRequest represents a network connection request
type NetworkConnectRequest struct {
	Container      string          `json:"Container"`
	EndpointConfig *EndpointConfig `json:"EndpointConfig,omitempty"`
}

// EndpointConfig represents endpoint configuration
type EndpointConfig struct {
	IPAMConfig *IPAMConfig `json:"IPAMConfig,omitempty"`
	Links      []string    `json:"Links,omitempty"`
	Aliases    []string    `json:"Aliases,omitempty"`
}

// IPAMConfig represents IPAM configuration for endpoint
type IPAMConfig struct {
	IPv4Address  string   `json:"IPv4Address,omitempty"`
	IPv6Address  string   `json:"IPv6Address,omitempty"`
	LinkLocalIPs []string `json:"LinkLocalIPs,omitempty"`
}

// NetworkDisconnectRequest represents a network disconnection request
type NetworkDisconnectRequest struct {
	Container string `json:"Container"`
	Force     bool   `json:"Force,omitempty"`
}

// NetworkCreate handles POST /networks/create
func (h *handlers) NetworkCreate(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Network create request")

	// Parse request body
	var req NetworkCreateRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		api.WriteDockerError(w, http.StatusBadRequest, "Invalid JSON in request body")
		return
	}

	// Validate required parameters
	if req.Name == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Network name is required")
		return
	}

	// Create network
	networkStore := h.runtime.GetNetworkManager().GetStore()
	network, err := networkStore.Create(networks.CreateNetworkRequest{
		Name:       req.Name,
		Driver:     req.Driver,
		EnableIPv6: req.EnableIPv6,
		IPAM:       req.IPAM,
		Internal:   req.Internal,
		Attachable: req.Attachable,
		Ingress:    req.Ingress,
		Options:    req.Options,
		Labels:     req.Labels,
	})
	if err != nil {
		api.WriteDockerError(w, http.StatusConflict, err.Error())
		return
	}

	// Create bridge if using bridge driver
	if network.Driver == "bridge" {
		bridgeManager := h.runtime.GetNetworkManager().GetBridgeManager()
		_, err := bridgeManager.CreateBridge(network.ID, network.Name, "172.17.0.0/16", "172.17.0.1")
		if err != nil {
			h.logger.WithError(err).Error("Failed to create bridge")
			// Continue anyway, bridge creation is not critical for MVP
		}
	}

	// Build response
	verbose := getVerboseFromRequest(r)
	ctp96 := getCTP96FromRequest(r)
	response := h.buildNetworkCreateResponse(network, verbose, ctp96)

	// Publish event
	h.runtime.GetEventBus().PublishNetworkEvent(
		events.ActionCreate,
		network.ID,
		network.Name,
		map[string]string{
			"driver": network.Driver,
		},
		verbose,
	)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(response)
}

// NetworkList handles GET /networks
func (h *handlers) NetworkList(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Network list request")

	// Parse query parameters
	filters := r.URL.Query().Get("filters")
	_ = filters // TODO: implement filtering

	// Get networks
	networkStore := h.runtime.GetNetworkManager().GetStore()
	networkList := networkStore.List()

	// Build response
	verbose := getVerboseFromRequest(r)
	ctp96 := getCTP96FromRequest(r)
	networks := make([]*networks.Network, 0, len(networkList))
	for _, network := range networkList {
		net := network
		if verbose {
			// Add Hologram-specific data
			if net.XHologram == nil {
				net.XHologram = make(map[string]any)
			}
			net.XHologram["driver"] = "hologram"

			// Add CTP-96 session if enabled
			if ctp96 && net.Name == "ctp96" {
				net.XHologram["ctp96_session"] = fmt.Sprintf("ctp96_%s", net.ID[:8])
			}
		}
		networks = append(networks, net)
	}

	response := NetworkListResponse(networks)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(response)
}

// NetworkInspect handles GET /networks/{id}
func (h *handlers) NetworkInspect(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Network inspect request")

	// Get network ID from URL
	vars := mux.Vars(r)
	networkID := vars["id"]

	if networkID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Network ID is required")
		return
	}

	// Get network
	networkStore := h.runtime.GetNetworkManager().GetStore()
	network, exists := networkStore.Get(networkID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such network: %s", networkID))
		return
	}

	// Build response
	verbose := getVerboseFromRequest(r)
	ctp96 := getCTP96FromRequest(r)
	response := h.buildNetworkInspectResponse(network, verbose, ctp96)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(response)
}

// NetworkConnect handles POST /networks/{id}/connect
func (h *handlers) NetworkConnect(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Network connect request")

	// Get network ID from URL
	vars := mux.Vars(r)
	networkID := vars["id"]

	if networkID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Network ID is required")
		return
	}

	// Parse request body
	var req NetworkConnectRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		api.WriteDockerError(w, http.StatusBadRequest, "Invalid JSON in request body")
		return
	}

	// Validate required parameters
	if req.Container == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Get network
	networkStore := h.runtime.GetNetworkManager().GetStore()
	network, exists := networkStore.Get(networkID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such network: %s", networkID))
		return
	}

	// Connect container to network
	containerName := "/" + req.Container[:12]
	err := networkStore.Connect(networkID, req.Container, containerName)
	if err != nil {
		api.WriteDockerError(w, http.StatusConflict, err.Error())
		return
	}

	// Connect to bridge if using bridge driver
	if network.Driver == "bridge" {
		bridgeManager := h.runtime.GetNetworkManager().GetBridgeManager()
		_, err := bridgeManager.ConnectContainer(networkID, req.Container, fmt.Sprintf("endpoint_%s_%s", networkID, req.Container))
		if err != nil {
			h.logger.WithError(err).Error("Failed to connect container to bridge")
			// Continue anyway, bridge connection is not critical for MVP
		}
	}

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishNetworkEvent(
		events.ActionConnect,
		networkID,
		network.Name,
		map[string]string{
			"container": req.Container,
		},
		verbose,
	)

	w.WriteHeader(http.StatusOK)
}

// NetworkDisconnect handles POST /networks/{id}/disconnect
func (h *handlers) NetworkDisconnect(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Network disconnect request")

	// Get network ID from URL
	vars := mux.Vars(r)
	networkID := vars["id"]

	if networkID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Network ID is required")
		return
	}

	// Parse request body
	var req NetworkDisconnectRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		api.WriteDockerError(w, http.StatusBadRequest, "Invalid JSON in request body")
		return
	}

	// Validate required parameters
	if req.Container == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Get network
	networkStore := h.runtime.GetNetworkManager().GetStore()
	network, exists := networkStore.Get(networkID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such network: %s", networkID))
		return
	}

	// Disconnect container from network
	err := networkStore.Disconnect(networkID, req.Container)
	if err != nil {
		api.WriteDockerError(w, http.StatusConflict, err.Error())
		return
	}

	// Disconnect from bridge if using bridge driver
	if network.Driver == "bridge" {
		bridgeManager := h.runtime.GetNetworkManager().GetBridgeManager()
		err := bridgeManager.DisconnectContainer(networkID, req.Container)
		if err != nil {
			h.logger.WithError(err).Error("Failed to disconnect container from bridge")
			// Continue anyway, bridge disconnection is not critical for MVP
		}
	}

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishNetworkEvent(
		events.ActionDisconnect,
		networkID,
		network.Name,
		map[string]string{
			"container": req.Container,
		},
		verbose,
	)

	w.WriteHeader(http.StatusOK)
}

// NetworkDelete handles DELETE /networks/{id}
func (h *handlers) NetworkDelete(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Network delete request")

	// Get network ID from URL
	vars := mux.Vars(r)
	networkID := vars["id"]

	if networkID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Network ID is required")
		return
	}

	// Get network
	networkStore := h.runtime.GetNetworkManager().GetStore()
	network, exists := networkStore.Get(networkID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such network: %s", networkID))
		return
	}

	// Remove bridge if using bridge driver
	if network.Driver == "bridge" {
		bridgeManager := h.runtime.GetNetworkManager().GetBridgeManager()
		err := bridgeManager.RemoveBridge(networkID)
		if err != nil {
			h.logger.WithError(err).Error("Failed to remove bridge")
			// Continue anyway, bridge removal is not critical for MVP
		}
	}

	// Remove network
	err := networkStore.Remove(networkID)
	if err != nil {
		api.WriteDockerError(w, http.StatusConflict, err.Error())
		return
	}

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishNetworkEvent(
		events.ActionDelete,
		networkID,
		network.Name,
		map[string]string{
			"driver": network.Driver,
		},
		verbose,
	)

	w.WriteHeader(http.StatusNoContent)
}

// Helper methods

func (h *handlers) buildNetworkCreateResponse(network *networks.Network, verbose, ctp96 bool) NetworkCreateResponse {
	response := NetworkCreateResponse{
		ID:         network.ID,
		Name:       network.Name,
		Created:    network.Created,
		Scope:      network.Scope,
		Driver:     network.Driver,
		EnableIPv6: network.EnableIPv6,
		IPAM:       network.IPAM,
		Internal:   network.Internal,
		Attachable: network.Attachable,
		Ingress:    network.Ingress,
		ConfigFrom: network.ConfigFrom,
		ConfigOnly: network.ConfigOnly,
		Containers: network.Containers,
		Options:    network.Options,
		Labels:     network.Labels,
	}

	// Add Hologram-specific data if verbose
	if verbose {
		response.XHologram = make(map[string]any)
		response.XHologram["driver"] = "hologram"
		response.XHologram["created_by"] = "hologramd"

		// Add CTP-96 session if enabled
		if ctp96 && network.Name == "ctp96" {
			response.XHologram["ctp96_session"] = fmt.Sprintf("ctp96_%s", network.ID[:8])
		}
	}

	return response
}

func (h *handlers) buildNetworkInspectResponse(network *networks.Network, verbose, ctp96 bool) NetworkInspectResponse {
	response := NetworkInspectResponse{
		ID:         network.ID,
		Name:       network.Name,
		Created:    network.Created,
		Scope:      network.Scope,
		Driver:     network.Driver,
		EnableIPv6: network.EnableIPv6,
		IPAM:       network.IPAM,
		Internal:   network.Internal,
		Attachable: network.Attachable,
		Ingress:    network.Ingress,
		ConfigFrom: network.ConfigFrom,
		ConfigOnly: network.ConfigOnly,
		Containers: network.Containers,
		Options:    network.Options,
		Labels:     network.Labels,
	}

	// Add Hologram-specific data if verbose
	if verbose {
		response.XHologram = make(map[string]any)
		response.XHologram["driver"] = "hologram"
		response.XHologram["created_by"] = "hologramd"

		// Add CTP-96 session if enabled
		if ctp96 && network.Name == "ctp96" {
			response.XHologram["ctp96_session"] = fmt.Sprintf("ctp96_%s", network.ID[:8])
		}
	}

	return response
}

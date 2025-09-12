package server

import (
	"encoding/json"
	"fmt"
	"net/http"

	"github.com/gorilla/mux"
	"github.com/hologram/engine/internal/api"
	"github.com/hologram/engine/internal/events"
	"github.com/hologram/engine/internal/volumes"
)

// VolumeCreateRequest represents a volume creation request
type VolumeCreateRequest struct {
	Name       string            `json:"Name,omitempty"`
	Driver     string            `json:"Driver,omitempty"`
	DriverOpts map[string]string `json:"DriverOpts,omitempty"`
	Labels     map[string]string `json:"Labels,omitempty"`
}

// VolumeCreateResponse represents a volume creation response
type VolumeCreateResponse struct {
	Name       string             `json:"Name"`
	Driver     string             `json:"Driver"`
	Mountpoint string             `json:"Mountpoint"`
	CreatedAt  string             `json:"CreatedAt"`
	Status     map[string]string  `json:"Status,omitempty"`
	Labels     map[string]string  `json:"Labels,omitempty"`
	Scope      string             `json:"Scope"`
	Options    map[string]string  `json:"Options,omitempty"`
	UsageData  *volumes.UsageData `json:"UsageData,omitempty"`
	XHologram  map[string]any     `json:"XHologram,omitempty"`
}

// VolumeListResponse represents a volume list response
type VolumeListResponse struct {
	Volumes  []*volumes.Volume `json:"Volumes"`
	Warnings []string          `json:"Warnings"`
}

// VolumeInspectResponse represents a volume inspect response
type VolumeInspectResponse struct {
	Name       string             `json:"Name"`
	Driver     string             `json:"Driver"`
	Mountpoint string             `json:"Mountpoint"`
	CreatedAt  string             `json:"CreatedAt"`
	Status     map[string]string  `json:"Status,omitempty"`
	Labels     map[string]string  `json:"Labels,omitempty"`
	Scope      string             `json:"Scope"`
	Options    map[string]string  `json:"Options,omitempty"`
	UsageData  *volumes.UsageData `json:"UsageData,omitempty"`
	XHologram  map[string]any     `json:"XHologram,omitempty"`
}

// VolumeCreate handles POST /volumes/create
func (h *handlers) VolumeCreate(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Volume create request")

	// Parse request body
	var req VolumeCreateRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		api.WriteDockerError(w, http.StatusBadRequest, "Invalid JSON in request body")
		return
	}

	// Create volume
	volumeStore := h.runtime.GetVolumeManager().GetStore()
	volume, err := volumeStore.Create(volumes.CreateVolumeRequest{
		Name:       req.Name,
		Driver:     req.Driver,
		DriverOpts: req.DriverOpts,
		Labels:     req.Labels,
	})
	if err != nil {
		api.WriteDockerError(w, http.StatusConflict, err.Error())
		return
	}

	// Build response
	verbose := getVerboseFromRequest(r)
	response := h.buildVolumeCreateResponse(volume, verbose)

	// Publish event
	h.runtime.GetEventBus().PublishVolumeEvent(
		events.ActionCreate,
		volume.Name,
		map[string]string{
			"driver": volume.Driver,
		},
		verbose,
	)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(response)
}

// VolumeList handles GET /volumes
func (h *handlers) VolumeList(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Volume list request")

	// Parse query parameters
	filters := r.URL.Query().Get("filters")
	_ = filters // TODO: implement filtering

	// Get volumes
	volumeStore := h.runtime.GetVolumeManager().GetStore()
	volumeList := volumeStore.List()

	// Build response
	verbose := getVerboseFromRequest(r)
	volumes := make([]*volumes.Volume, 0, len(volumeList))
	for _, volume := range volumeList {
		vol := volume
		if verbose {
			// Add Hologram-specific data
			if vol.XHologram == nil {
				vol.XHologram = make(map[string]any)
			}
			vol.XHologram["driver"] = "hologram"
		}
		volumes = append(volumes, vol)
	}

	response := VolumeListResponse{
		Volumes:  volumes,
		Warnings: []string{},
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(response)
}

// VolumeInspect handles GET /volumes/{name}
func (h *handlers) VolumeInspect(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Volume inspect request")

	// Get volume name from URL
	vars := mux.Vars(r)
	volumeName := vars["name"]

	if volumeName == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Volume name is required")
		return
	}

	// Get volume
	volumeStore := h.runtime.GetVolumeManager().GetStore()
	volume, exists := volumeStore.Get(volumeName)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such volume: %s", volumeName))
		return
	}

	// Build response
	verbose := getVerboseFromRequest(r)
	response := h.buildVolumeInspectResponse(volume, verbose)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(response)
}

// VolumeDelete handles DELETE /volumes/{name}
func (h *handlers) VolumeDelete(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Volume delete request")

	// Get volume name from URL
	vars := mux.Vars(r)
	volumeName := vars["name"]

	if volumeName == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Volume name is required")
		return
	}

	// Parse query parameters
	force := r.URL.Query().Get("force") == "true"

	// Get volume
	volumeStore := h.runtime.GetVolumeManager().GetStore()
	volume, exists := volumeStore.Get(volumeName)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such volume: %s", volumeName))
		return
	}

	// Remove volume
	err := volumeStore.Remove(volumeName)
	if err != nil {
		if force {
			// Force remove even if in use
			// TODO: implement force removal logic
		}
		api.WriteDockerError(w, http.StatusConflict, err.Error())
		return
	}

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishVolumeEvent(
		events.ActionDelete,
		volumeName,
		map[string]string{
			"driver": volume.Driver,
		},
		verbose,
	)

	w.WriteHeader(http.StatusNoContent)
}

// VolumePrune handles POST /volumes/prune
func (h *handlers) VolumePrune(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Volume prune request")

	// Parse query parameters
	filters := r.URL.Query().Get("filters")
	_ = filters // TODO: implement filtering

	// Prune volumes
	volumeStore := h.runtime.GetVolumeManager().GetStore()
	removed, err := volumeStore.Prune()
	if err != nil {
		api.WriteDockerError(w, http.StatusInternalServerError, err.Error())
		return
	}

	// Publish events for removed volumes
	verbose := getVerboseFromRequest(r)
	for _, volumeName := range removed {
		h.runtime.GetEventBus().PublishVolumeEvent(
			events.ActionDelete,
			volumeName,
			map[string]string{},
			verbose,
		)
	}

	// Build response
	response := map[string]interface{}{
		"VolumesDeleted": removed,
		"SpaceReclaimed": 0, // TODO: calculate actual space reclaimed
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(response)
}

// Helper methods

func (h *handlers) buildVolumeCreateResponse(volume *volumes.Volume, verbose bool) VolumeCreateResponse {
	response := VolumeCreateResponse{
		Name:       volume.Name,
		Driver:     volume.Driver,
		Mountpoint: volume.Mountpoint,
		CreatedAt:  volume.CreatedAt,
		Status:     volume.Status,
		Labels:     volume.Labels,
		Scope:      volume.Scope,
		Options:    volume.Options,
		UsageData:  volume.UsageData,
	}

	// Add Hologram-specific data if verbose
	if verbose {
		response.XHologram = make(map[string]any)
		response.XHologram["driver"] = "hologram"
		response.XHologram["created_by"] = "hologramd"
	}

	return response
}

func (h *handlers) buildVolumeInspectResponse(volume *volumes.Volume, verbose bool) VolumeInspectResponse {
	response := VolumeInspectResponse{
		Name:       volume.Name,
		Driver:     volume.Driver,
		Mountpoint: volume.Mountpoint,
		CreatedAt:  volume.CreatedAt,
		Status:     volume.Status,
		Labels:     volume.Labels,
		Scope:      volume.Scope,
		Options:    volume.Options,
		UsageData:  volume.UsageData,
	}

	// Add Hologram-specific data if verbose
	if verbose {
		response.XHologram = make(map[string]any)
		response.XHologram["driver"] = "hologram"
		response.XHologram["created_by"] = "hologramd"
	}

	return response
}

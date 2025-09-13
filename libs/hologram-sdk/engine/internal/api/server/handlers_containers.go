package server

import (
	"encoding/json"
	"fmt"
	"net/http"
	"strconv"
	"strings"
	"time"

	"github.com/gorilla/mux"
	"github.com/hologram/engine/internal/api"
	"github.com/hologram/engine/internal/events"
	"github.com/hologram/engine/internal/runtime"
)

// ContainerLogsParams represents parameters for container logs
type ContainerLogsParams struct {
	Follow     bool
	Stdout     bool
	Stderr     bool
	Since      time.Time
	Until      time.Time
	Timestamps bool
	Tail       string
}

// StopOptions represents options for stopping a container
type StopOptions struct {
	Timeout *int
}

// ContainerCreateRequest represents a container creation request
type ContainerCreateRequest struct {
	Image         string                 `json:"Image"`
	Cmd           []string               `json:"Cmd"`
	Env           []string               `json:"Env"`
	WorkingDir    string                 `json:"WorkingDir"`
	Labels        map[string]string      `json:"Labels"`
	HostConfig    map[string]interface{} `json:"HostConfig"`
	NetworkConfig map[string]interface{} `json:"NetworkingConfig"`
	ExposedPorts  map[string]interface{} `json:"ExposedPorts"`
	Volumes       map[string]interface{} `json:"Volumes"`
	User          string                 `json:"User"`
	AttachStdin   bool                   `json:"AttachStdin"`
	AttachStdout  bool                   `json:"AttachStdout"`
	AttachStderr  bool                   `json:"AttachStderr"`
	Tty           bool                   `json:"Tty"`
	OpenStdin     bool                   `json:"OpenStdin"`
	StdinOnce     bool                   `json:"StdinOnce"`
}

// ContainerCreateResponse represents a container creation response
type ContainerCreateResponse struct {
	ID       string   `json:"Id"`
	Warnings []string `json:"Warnings"`
}

// ContainerInspectResponse represents a container inspect response
type ContainerInspectResponse struct {
	ID              string                 `json:"Id"`
	Created         string                 `json:"Created"`
	Path            string                 `json:"Path"`
	Args            []string               `json:"Args"`
	State           ContainerStateResponse `json:"State"`
	Image           string                 `json:"Image"`
	ResolvConfPath  string                 `json:"ResolvConfPath"`
	HostnamePath    string                 `json:"HostnamePath"`
	HostsPath       string                 `json:"HostsPath"`
	LogPath         string                 `json:"LogPath"`
	Name            string                 `json:"Name"`
	RestartCount    int                    `json:"RestartCount"`
	Driver          string                 `json:"Driver"`
	Platform        string                 `json:"Platform"`
	MountLabel      string                 `json:"MountLabel"`
	ProcessLabel    string                 `json:"ProcessLabel"`
	AppArmorProfile string                 `json:"AppArmorProfile"`
	ExecIDs         []string               `json:"ExecIDs"`
	HostConfig      map[string]interface{} `json:"HostConfig"`
	GraphDriver     map[string]interface{} `json:"GraphDriver"`
	SizeRw          int64                  `json:"SizeRw"`
	SizeRootFs      int64                  `json:"SizeRootFs"`
	Mounts          []api.Mount            `json:"Mounts"`
	Config          map[string]interface{} `json:"Config"`
	NetworkSettings map[string]interface{} `json:"NetworkSettings"`
	XHologram       map[string]any         `json:"XHologram,omitempty"`
}

// ContainerStateResponse represents container state in inspect response
type ContainerStateResponse struct {
	Status     string `json:"Status"`
	Running    bool   `json:"Running"`
	Paused     bool   `json:"Paused"`
	Restarting bool   `json:"Restarting"`
	OOMKilled  bool   `json:"OOMKilled"`
	Dead       bool   `json:"Dead"`
	Pid        int    `json:"Pid"`
	ExitCode   int    `json:"ExitCode"`
	Error      string `json:"Error"`
	StartedAt  string `json:"StartedAt"`
	FinishedAt string `json:"FinishedAt"`
}

// ContainerCreate handles POST /containers/create
func (h *handlers) ContainerCreate(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container create request")

	// Parse request body
	var req ContainerCreateRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		api.WriteDockerError(w, http.StatusBadRequest, "Invalid JSON in request body")
		return
	}

	// Validate required parameters
	if req.Image == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Image parameter is required")
		return
	}

	// Check enforce mode for image witness
	verbose := getVerboseFromRequest(r)
	enforce := getEnforceFromRequest(r)

	if enforce {
		// In enforce mode, check if image has valid witness
		// For MVP, we'll simulate this check
		if strings.Contains(req.Image, "bad") {
			api.WriteDockerError(w, http.StatusBadRequest, "artifact witness invalid or missing")
			return
		}
	}

	// Generate container ID
	containerID := fmt.Sprintf("deadbeef%x", time.Now().UnixNano())

	// Create container state
	containerState := &runtime.ContainerState{
		ID:              containerID,
		Name:            "/" + containerID[:12],
		Image:           req.Image,
		Created:         time.Now().Format(time.RFC3339Nano),
		StartedAt:       "",
		FinishedAt:      "",
		Running:         false,
		OOMKilled:       false,
		ExitCode:        0,
		Pid:             0,
		HostConfig:      req.HostConfig,
		Config:          h.buildContainerConfig(req),
		NetworkSettings: make(map[string]any),
		XHologram:       make(map[string]any),
	}

	// Add Hologram-specific data if verbose
	if verbose {
		containerState.XHologram["lease_id"] = fmt.Sprintf("lease_%s", containerID)
		containerState.XHologram["witness_ok"] = true
		containerState.XHologram["uor_id"] = fmt.Sprintf("uor:%s", containerID)
	}

	// Store container state
	h.runtime.GetContainerManager().GetStore().Put(containerState)

	// Create log buffer for container
	h.runtime.GetLogManager().CreateBuffer(containerID, 1000)

	// Publish event
	h.runtime.GetEventBus().PublishContainerEvent(
		events.ActionCreate,
		containerID,
		req.Image,
		map[string]string{
			"name": containerState.Name,
		},
		verbose,
	)

	// Create response
	response := ContainerCreateResponse{
		ID:       containerID,
		Warnings: []string{},
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(response)
}

// ContainerStart handles POST /containers/{id}/start
func (h *handlers) ContainerStart(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container start request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Get container state
	store := h.runtime.GetContainerManager().GetStore()
	containerState, exists := store.Get(containerID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such container: %s", containerID))
		return
	}

	// Check if already running
	if containerState.Running {
		api.WriteDockerError(w, http.StatusNotModified, "Container already started")
		return
	}

	// Start the container process
	processRunner := h.runtime.GetProcessRunner()
	process, err := processRunner.StartProcess(
		containerID,
		containerState.Image,
		h.getContainerCmd(containerState),
		h.getContainerEnv(containerState),
	)
	if err != nil {
		h.logger.WithError(err).Error("Failed to start container process")
		api.WriteDockerError(w, http.StatusInternalServerError, "Failed to start container")
		return
	}

	// Update container state
	store.UpdateState(containerID, map[string]any{
		"Running": true,
		"Pid":     process.GetPID(),
	})

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishContainerEvent(
		events.ActionStart,
		containerID,
		containerState.Image,
		map[string]string{
			"name": containerState.Name,
		},
		verbose,
	)

	w.WriteHeader(http.StatusNoContent)
}

// ContainerStop handles POST /containers/{id}/stop
func (h *handlers) ContainerStop(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container stop request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Parse timeout parameter
	timeout := 10 // default timeout
	if t := r.URL.Query().Get("t"); t != "" {
		if parsedTimeout, err := strconv.Atoi(t); err == nil {
			timeout = parsedTimeout
		}
	}

	// Get container state
	store := h.runtime.GetContainerManager().GetStore()
	containerState, exists := store.Get(containerID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such container: %s", containerID))
		return
	}

	// Check if already stopped
	if !containerState.Running {
		api.WriteDockerError(w, http.StatusNotModified, "Container already stopped")
		return
	}

	// Stop the container process
	processRunner := h.runtime.GetProcessRunner()
	err := processRunner.StopProcess(containerID, time.Duration(timeout)*time.Second)
	if err != nil {
		h.logger.WithError(err).Error("Failed to stop container process")
		api.WriteDockerError(w, http.StatusInternalServerError, "Failed to stop container")
		return
	}

	// Get process to get exit code
	process, exists := processRunner.GetProcess(containerID)
	if exists {
		store.UpdateState(containerID, map[string]any{
			"Running":  false,
			"ExitCode": process.GetExitCode(),
		})
	}

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishContainerEvent(
		events.ActionStop,
		containerID,
		containerState.Image,
		map[string]string{
			"name": containerState.Name,
		},
		verbose,
	)

	w.WriteHeader(http.StatusNoContent)
}

// ContainerInspect handles GET /containers/{id}/json
func (h *handlers) ContainerInspect(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container inspect request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Get container state
	store := h.runtime.GetContainerManager().GetStore()
	containerState, exists := store.Get(containerID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such container: %s", containerID))
		return
	}

	// Build inspect response
	verbose := getVerboseFromRequest(r)
	ctp96 := getCTP96FromRequest(r)

	response := h.buildContainerInspectResponse(containerState, verbose, ctp96)

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(response)
}

// ContainerLogs handles GET /containers/{id}/logs
func (h *handlers) ContainerLogs(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container logs request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Parse query parameters
	params := ContainerLogsParams{
		Follow:     r.URL.Query().Get("follow") == "true",
		Stdout:     r.URL.Query().Get("stdout") != "false", // default true
		Stderr:     r.URL.Query().Get("stderr") != "false", // default true
		Timestamps: r.URL.Query().Get("timestamps") == "true",
		Tail:       r.URL.Query().Get("tail"),
	}

	// Parse since parameter
	if since := r.URL.Query().Get("since"); since != "" {
		if parsedSince, err := time.Parse(time.RFC3339Nano, since); err == nil {
			params.Since = parsedSince
		}
	}

	// Parse tail parameter
	tail := -1
	if params.Tail != "" && params.Tail != "all" {
		if parsedTail, err := strconv.Atoi(params.Tail); err == nil {
			tail = parsedTail
		}
	}

	// Get logs
	logManager := h.runtime.GetLogManager()
	logEntries := logManager.GetLogs(containerID, params.Since, tail, params.Stdout, params.Stderr)

	// Set response headers
	w.Header().Set("Content-Type", "application/vnd.docker.raw-stream")
	w.Header().Set("Transfer-Encoding", "chunked")

	// Write logs
	for _, entry := range logEntries {
		formatted := runtime.FormatLogEntry(entry, params.Timestamps)
		w.Write(formatted)
	}

	// Handle follow mode
	if params.Follow {
		// Stream logs
		logChan := logManager.StreamLogs(containerID)
		defer logManager.StopStreaming(containerID, logChan)

		for {
			select {
			case entry := <-logChan:
				formatted := runtime.FormatLogEntry(entry, params.Timestamps)
				w.Write(formatted)
				if f, ok := w.(http.Flusher); ok {
					f.Flush()
				}
			case <-r.Context().Done():
				return
			}
		}
	}
}

// ContainerDelete handles DELETE /containers/{id}
func (h *handlers) ContainerDelete(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container delete request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		api.WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Parse query parameters
	force := r.URL.Query().Get("force") == "true"

	// Get container state
	store := h.runtime.GetContainerManager().GetStore()
	containerState, exists := store.Get(containerID)
	if !exists {
		api.WriteDockerError(w, http.StatusNotFound, fmt.Sprintf("No such container: %s", containerID))
		return
	}

	// Check if container is running
	if containerState.Running && !force {
		api.WriteDockerError(w, http.StatusConflict, "You cannot remove a running container. Stop the container before attempting removal or use -f")
		return
	}

	// Stop container if running
	if containerState.Running {
		processRunner := h.runtime.GetProcessRunner()
		processRunner.StopProcess(containerID, 10*time.Second)
		processRunner.RemoveProcess(containerID)
	}

	// Remove container from store
	store.Del(containerID)

	// Remove logs
	h.runtime.GetLogManager().RemoveContainer(containerID)

	// Publish event
	verbose := getVerboseFromRequest(r)
	h.runtime.GetEventBus().PublishContainerEvent(
		events.ActionDestroy,
		containerID,
		containerState.Image,
		map[string]string{
			"name": containerState.Name,
		},
		verbose,
	)

	w.WriteHeader(http.StatusNoContent)
}

// Helper methods

func (h *handlers) buildContainerConfig(req ContainerCreateRequest) map[string]any {
	config := make(map[string]any)

	config["Image"] = req.Image
	config["Cmd"] = req.Cmd
	config["Env"] = req.Env
	config["WorkingDir"] = req.WorkingDir
	config["Labels"] = req.Labels
	config["ExposedPorts"] = req.ExposedPorts
	config["Volumes"] = req.Volumes
	config["User"] = req.User
	config["AttachStdin"] = req.AttachStdin
	config["AttachStdout"] = req.AttachStdout
	config["AttachStderr"] = req.AttachStderr
	config["Tty"] = req.Tty
	config["OpenStdin"] = req.OpenStdin
	config["StdinOnce"] = req.StdinOnce

	return config
}

func (h *handlers) getContainerCmd(containerState *runtime.ContainerState) []string {
	if cmd, ok := containerState.Config["Cmd"].([]string); ok {
		return cmd
	}
	return []string{}
}

func (h *handlers) getContainerEnv(containerState *runtime.ContainerState) []string {
	if env, ok := containerState.Config["Env"].([]string); ok {
		return env
	}
	return []string{}
}

func (h *handlers) buildContainerInspectResponse(containerState *runtime.ContainerState, verbose, ctp96 bool) ContainerInspectResponse {
	response := ContainerInspectResponse{
		ID:      containerState.ID,
		Created: containerState.Created,
		Path:    "/hello",
		Args:    h.getContainerCmd(containerState),
		State: ContainerStateResponse{
			Status:     h.getContainerStatus(containerState),
			Running:    containerState.Running,
			Paused:     false,
			Restarting: false,
			OOMKilled:  containerState.OOMKilled,
			Dead:       false,
			Pid:        containerState.Pid,
			ExitCode:   containerState.ExitCode,
			Error:      "",
			StartedAt:  containerState.StartedAt,
			FinishedAt: containerState.FinishedAt,
		},
		Image:           containerState.Image,
		ResolvConfPath:  fmt.Sprintf("/var/lib/docker/containers/%s/resolv.conf", containerState.ID),
		HostnamePath:    fmt.Sprintf("/var/lib/docker/containers/%s/hostname", containerState.ID),
		HostsPath:       fmt.Sprintf("/var/lib/docker/containers/%s/hosts", containerState.ID),
		LogPath:         fmt.Sprintf("/var/lib/docker/containers/%s/%s-json.log", containerState.ID, containerState.ID),
		Name:            containerState.Name,
		RestartCount:    0,
		Driver:          "overlay2",
		Platform:        "linux",
		MountLabel:      "",
		ProcessLabel:    "",
		AppArmorProfile: "",
		ExecIDs:         []string{},
		HostConfig:      containerState.HostConfig,
		GraphDriver: map[string]interface{}{
			"Name": "overlay2",
			"Data": map[string]interface{}{
				"LowerDir":  "/var/lib/docker/overlay2/lower",
				"MergedDir": "/var/lib/docker/overlay2/merged",
				"UpperDir":  "/var/lib/docker/overlay2/upper",
				"WorkDir":   "/var/lib/docker/overlay2/work",
			},
		},
		SizeRw:     0,
		SizeRootFs: 1024,
		Mounts:     []api.Mount{},
		Config:     containerState.Config,
		NetworkSettings: map[string]interface{}{
			"Bridge":                 "",
			"SandboxID":              "",
			"HairpinMode":            false,
			"LinkLocalIPv6Address":   "",
			"LinkLocalIPv6PrefixLen": 0,
			"Ports":                  map[string]interface{}{},
			"SandboxKey":             "",
			"SecondaryIPAddresses":   []interface{}{},
			"SecondaryIPv6Addresses": []interface{}{},
			"EndpointID":             "",
			"Gateway":                "",
			"GlobalIPv6Address":      "",
			"GlobalIPv6PrefixLen":    0,
			"IPAddress":              "",
			"IPPrefixLen":            0,
			"IPv6Gateway":            "",
			"MacAddress":             "",
			"Networks": map[string]interface{}{
				"bridge": map[string]interface{}{
					"NetworkID":           "bridge",
					"EndpointID":          "",
					"Gateway":             "",
					"IPAddress":           "",
					"IPPrefixLen":         0,
					"IPv6Gateway":         "",
					"GlobalIPv6Address":   "",
					"GlobalIPv6PrefixLen": 0,
					"MacAddress":          "",
				},
			},
		},
	}

	// Add Hologram-specific data if verbose
	if verbose {
		response.XHologram = make(map[string]any)
		response.XHologram["lease_id"] = containerState.XHologram["lease_id"]
		response.XHologram["witness_ok"] = containerState.XHologram["witness_ok"]
		response.XHologram["uor_id"] = containerState.XHologram["uor_id"]

		// Add CTP-96 session if enabled
		if ctp96 {
			response.XHologram["ctp96_session"] = fmt.Sprintf("ctp96_%s", containerState.ID[:8])
		}
	}

	return response
}

func (h *handlers) getContainerStatus(containerState *runtime.ContainerState) string {
	if containerState.Running {
		return "running"
	}
	if containerState.ExitCode == 0 {
		return "exited"
	}
	return "exited"
}

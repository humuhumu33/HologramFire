package api

import (
	"encoding/json"
	"fmt"
	"net/http"
	"strconv"
	"time"

	"github.com/gorilla/mux"
	"github.com/hologram/engine/internal/runtime"
	"github.com/sirupsen/logrus"
)

// Container represents a Docker container
type Container struct {
	ID              string                 `json:"Id"`
	Names           []string               `json:"Names"`
	Image           string                 `json:"Image"`
	ImageID         string                 `json:"ImageID"`
	Command         string                 `json:"Command"`
	Created         int64                  `json:"Created"`
	State           string                 `json:"State"`
	Status          string                 `json:"Status"`
	Ports           []Port                 `json:"Ports"`
	Labels          map[string]string      `json:"Labels"`
	SizeRw          int64                  `json:"SizeRw"`
	SizeRootFs      int64                  `json:"SizeRootFs"`
	HostConfig      map[string]interface{} `json:"HostConfig"`
	NetworkSettings map[string]interface{} `json:"NetworkSettings"`
	Mounts          []Mount                `json:"Mounts"`
}

// Port represents a container port
type Port struct {
	IP          string `json:"IP"`
	PrivatePort int    `json:"PrivatePort"`
	PublicPort  int    `json:"PublicPort"`
	Type        string `json:"Type"`
}

// Mount represents a container mount
type Mount struct {
	Type        string `json:"Type"`
	Name        string `json:"Name"`
	Source      string `json:"Source"`
	Destination string `json:"Destination"`
	Driver      string `json:"Driver"`
	Mode        string `json:"Mode"`
	RW          bool   `json:"RW"`
	Propagation string `json:"Propagation"`
}

// ContainerCreateParams represents parameters for container creation
type ContainerCreateParams struct {
	Image         string                 `json:"Image"`
	Cmd           []string               `json:"Cmd"`
	Env           []string               `json:"Env"`
	WorkingDir    string                 `json:"WorkingDir"`
	Labels        map[string]string      `json:"Labels"`
	HostConfig    map[string]interface{} `json:"HostConfig"`
	NetworkConfig map[string]interface{} `json:"NetworkingConfig"`
}

// ContainerInspect represents detailed container information
type ContainerInspect struct {
	ID              string                 `json:"Id"`
	Created         string                 `json:"Created"`
	Path            string                 `json:"Path"`
	Args            []string               `json:"Args"`
	State           ContainerState         `json:"State"`
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
	Mounts          []Mount                `json:"Mounts"`
	Config          map[string]interface{} `json:"Config"`
	NetworkSettings map[string]interface{} `json:"NetworkSettings"`
}

// ContainerState represents container state information
type ContainerState struct {
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

// ContainerList handles GET /containers/json
func (h *handlers) ContainerList(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container list request")

	// Parse query parameters
	all := r.URL.Query().Get("all") == "true"
	_ = r.URL.Query().Get("filters") // filters parameter available for future use

	// Get containers from runtime
	store := h.runtime.GetContainerManager().GetStore()
	containerStates := store.List()

	// Convert to Docker-compatible format
	containers := make([]Container, 0, len(containerStates))
	for _, state := range containerStates {
		// Only include running containers unless all=true
		if !all && !state.Running {
			continue
		}

		container := Container{
			ID:              state.ID,
			Names:           []string{state.Name},
			Image:           state.Image,
			ImageID:         fmt.Sprintf("sha256:%s", state.ID[:64]),
			Command:         "/hello", // Default command
			Created:         time.Now().Unix(),
			State:           h.getContainerStateString(state),
			Status:          h.getContainerStatusString(state),
			Ports:           []Port{},
			Labels:          map[string]string{},
			SizeRw:          0,
			SizeRootFs:      1024,
			HostConfig:      state.HostConfig,
			NetworkSettings: state.NetworkSettings,
			Mounts:          []Mount{},
		}
		containers = append(containers, container)
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(containers)
}

// ContainerCreate handles POST /containers/create
func (h *handlers) ContainerCreate(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container create request")

	// Parse request body
	var params ContainerCreateParams
	if err := json.NewDecoder(r.Body).Decode(&params); err != nil {
		WriteDockerError(w, http.StatusBadRequest, "Invalid JSON in request body")
		return
	}

	// Validate required parameters
	if params.Image == "" {
		WriteDockerError(w, http.StatusBadRequest, "Image parameter is required")
		return
	}

	// Generate a container ID
	containerID := fmt.Sprintf("deadbeef%x", time.Now().UnixNano())

	// Create container response
	response := map[string]interface{}{
		"Id":       containerID,
		"Warnings": []string{},
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(response)
}

// ContainerInspect handles GET /containers/{id}/json
func (h *handlers) ContainerInspect(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container inspect request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Create container inspect response
	inspect := ContainerInspect{
		ID:      containerID,
		Created: time.Now().Format(time.RFC3339Nano),
		Path:    "/hello",
		Args:    []string{},
		State: ContainerState{
			Status:     "running",
			Running:    true,
			Paused:     false,
			Restarting: false,
			OOMKilled:  false,
			Dead:       false,
			Pid:        12345,
			ExitCode:   0,
			Error:      "",
			StartedAt:  time.Now().Format(time.RFC3339Nano),
			FinishedAt: "0001-01-01T00:00:00Z",
		},
		Image:           "hello-world:latest",
		ResolvConfPath:  "/var/lib/docker/containers/" + containerID + "/resolv.conf",
		HostnamePath:    "/var/lib/docker/containers/" + containerID + "/hostname",
		HostsPath:       "/var/lib/docker/containers/" + containerID + "/hosts",
		LogPath:         "/var/lib/docker/containers/" + containerID + "/" + containerID + "-json.log",
		Name:            "/test-container",
		RestartCount:    0,
		Driver:          "overlay2",
		Platform:        "linux",
		MountLabel:      "",
		ProcessLabel:    "",
		AppArmorProfile: "",
		ExecIDs:         []string{},
		HostConfig: map[string]interface{}{
			"Binds":           []string{},
			"ContainerIDFile": "",
			"LogConfig": map[string]interface{}{
				"Type":   "json-file",
				"Config": map[string]interface{}{},
			},
			"NetworkMode":  "default",
			"PortBindings": map[string]interface{}{},
			"RestartPolicy": map[string]interface{}{
				"Name":              "no",
				"MaximumRetryCount": 0,
			},
			"AutoRemove":           false,
			"VolumeDriver":         "",
			"VolumesFrom":          []string{},
			"CapAdd":               []string{},
			"CapDrop":              []string{},
			"Dns":                  []string{},
			"DnsOptions":           []string{},
			"DnsSearch":            []string{},
			"ExtraHosts":           []string{},
			"GroupAdd":             []string{},
			"IpcMode":              "",
			"Cgroup":               "",
			"Links":                []string{},
			"OomKillDisable":       false,
			"PidMode":              "",
			"Privileged":           false,
			"PublishAllPorts":      false,
			"ReadonlyRootfs":       false,
			"SecurityOpt":          []string{},
			"UTSMode":              "",
			"UsernsMode":           "",
			"ShmSize":              67108864,
			"Runtime":              "runc",
			"ConsoleSize":          []int{0, 0},
			"Isolation":            "",
			"CpuShares":            0,
			"Memory":               0,
			"NanoCpus":             0,
			"CgroupParent":         "",
			"BlkioWeight":          0,
			"BlkioWeightDevice":    []interface{}{},
			"BlkioDeviceReadBps":   []interface{}{},
			"BlkioDeviceWriteBps":  []interface{}{},
			"BlkioDeviceReadIOps":  []interface{}{},
			"BlkioDeviceWriteIOps": []interface{}{},
			"CpuPeriod":            0,
			"CpuQuota":             0,
			"CpuRealtimePeriod":    0,
			"CpuRealtimeRuntime":   0,
			"CpusetCpus":           "",
			"CpusetMems":           "",
			"Devices":              []interface{}{},
			"DeviceCgroupRules":    []string{},
			"DeviceRequests":       []interface{}{},
			"KernelMemory":         0,
			"KernelMemoryTCP":      0,
			"MemoryReservation":    0,
			"MemorySwap":           0,
			"MemorySwappiness":     nil,
			"PidsLimit":            nil,
			"Ulimits":              []interface{}{},
			"CpuCount":             0,
			"CpuPercent":           0,
			"IOMaximumIOps":        0,
			"IOMaximumBandwidth":   0,
		},
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
		Mounts:     []Mount{},
		Config: map[string]interface{}{
			"Hostname":     containerID[:12],
			"Domainname":   "",
			"User":         "",
			"AttachStdin":  false,
			"AttachStdout": true,
			"AttachStderr": true,
			"Tty":          false,
			"OpenStdin":    false,
			"StdinOnce":    false,
			"Env":          []string{"PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"},
			"Cmd":          []string{"/hello"},
			"Image":        "hello-world:latest",
			"Volumes":      map[string]interface{}{},
			"WorkingDir":   "",
			"Entrypoint":   nil,
			"OnBuild":      nil,
			"Labels":       map[string]string{},
		},
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

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(inspect)
}

// ContainerStart handles POST /containers/{id}/start
func (h *handlers) ContainerStart(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container start request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// For now, just return success
	// In a real implementation, this would start the container
	w.WriteHeader(http.StatusNoContent)
}

// ContainerStop handles POST /containers/{id}/stop
func (h *handlers) ContainerStop(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container stop request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Parse timeout parameter
	timeout := 10 // default timeout
	if t := r.URL.Query().Get("t"); t != "" {
		if parsedTimeout, err := strconv.Atoi(t); err == nil {
			timeout = parsedTimeout
		}
	}

	h.logger.WithFields(logrus.Fields{
		"container_id": containerID,
		"timeout":      timeout,
	}).Info("Stopping container")

	// For now, just return success
	// In a real implementation, this would stop the container
	w.WriteHeader(http.StatusNoContent)
}

// ContainerLogs handles GET /containers/{id}/logs
func (h *handlers) ContainerLogs(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container logs request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Parse query parameters
	follow := r.URL.Query().Get("follow") == "true"
	stdout := r.URL.Query().Get("stdout") == "true"
	stderr := r.URL.Query().Get("stderr") == "true"
	timestamps := r.URL.Query().Get("timestamps") == "true"
	tail := r.URL.Query().Get("tail")

	h.logger.WithFields(logrus.Fields{
		"container_id": containerID,
		"follow":       follow,
		"stdout":       stdout,
		"stderr":       stderr,
		"timestamps":   timestamps,
		"tail":         tail,
	}).Info("Getting container logs")

	// Set response headers
	w.Header().Set("Content-Type", "application/vnd.docker.raw-stream")
	w.Header().Set("Transfer-Encoding", "chunked")

	// For now, return sample logs
	// In a real implementation, this would stream actual container logs
	sampleLogs := "Hello from Docker!\nThis message shows that your installation appears to be working correctly.\n"

	if timestamps {
		timestamp := time.Now().Format(time.RFC3339Nano)
		sampleLogs = fmt.Sprintf("%s %s", timestamp, sampleLogs)
	}

	w.Write([]byte(sampleLogs))
}

// ContainerDelete handles DELETE /containers/{id}
func (h *handlers) ContainerDelete(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Container delete request")

	// Get container ID from URL
	vars := mux.Vars(r)
	containerID := vars["id"]

	if containerID == "" {
		WriteDockerError(w, http.StatusBadRequest, "Container ID is required")
		return
	}

	// Parse query parameters
	force := r.URL.Query().Get("force") == "true"
	v := r.URL.Query().Get("v") == "true"

	h.logger.WithFields(logrus.Fields{
		"container_id": containerID,
		"force":        force,
		"v":            v,
	}).Info("Deleting container")

	// For now, just return success
	// In a real implementation, this would delete the container
	w.WriteHeader(http.StatusNoContent)
}

// Helper methods

func (h *handlers) getContainerStateString(containerState *runtime.ContainerState) string {
	if containerState.Running {
		return "running"
	}
	return "exited"
}

func (h *handlers) getContainerStatusString(containerState *runtime.ContainerState) string {
	if containerState.Running {
		return "Up 2 minutes"
	}
	return fmt.Sprintf("Exited (%d) 2 minutes ago", containerState.ExitCode)
}

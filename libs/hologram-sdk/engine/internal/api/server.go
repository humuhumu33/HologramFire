package api

import (
	"encoding/json"
	"net/http"

	"github.com/gorilla/mux"
	"github.com/hologram/engine/internal/runtime"
	"github.com/sirupsen/logrus"
)

// Server represents the API server
type Server struct {
	logger   *logrus.Logger
	runtime  *runtime.Runtime
	features runtime.HologramFeatures
	router   *mux.Router
	handlers *handlers
}

// NewServer creates a new API server
func NewServer(logger *logrus.Logger, rt *runtime.Runtime, features runtime.HologramFeatures) *Server {
	s := &Server{
		logger:   logger,
		runtime:  rt,
		features: features,
		router:   mux.NewRouter(),
		handlers: NewHandlers(logger, rt, features),
	}

	s.setupRoutes()
	return s
}

// Handler returns the HTTP handler
func (s *Server) Handler() http.Handler {
	return s.router
}

// setupRoutes sets up the API routes
func (s *Server) setupRoutes() {
	// Docker Engine API compatibility - exact paths
	s.router.HandleFunc("/_ping", s.handlePing).Methods("GET")
	s.router.HandleFunc("/version", s.handleVersion).Methods("GET")
	s.router.HandleFunc("/info", s.handleInfo).Methods("GET")

	// Docker Engine API v1.41 routes
	s.router.HandleFunc("/v1.41/images/json", s.handlers.ImageList).Methods("GET")
	s.router.HandleFunc("/v1.41/images/create", s.handlers.ImageCreate).Methods("POST")
	s.router.HandleFunc("/v1.41/containers/json", s.handlers.ContainerList).Methods("GET")
	s.router.HandleFunc("/v1.41/containers/create", s.handlers.ContainerCreate).Methods("POST")
	s.router.HandleFunc("/v1.41/containers/{id}/json", s.handlers.ContainerInspect).Methods("GET")
	s.router.HandleFunc("/v1.41/containers/{id}/start", s.handlers.ContainerStart).Methods("POST")
	s.router.HandleFunc("/v1.41/containers/{id}/stop", s.handlers.ContainerStop).Methods("POST")
	s.router.HandleFunc("/v1.41/containers/{id}/logs", s.handlers.ContainerLogs).Methods("GET")
	s.router.HandleFunc("/v1.41/containers/{id}", s.handlers.ContainerDelete).Methods("DELETE")
	s.router.HandleFunc("/v1.41/events", s.handlers.EventsHandler).Methods("GET")
	s.router.HandleFunc("/v1.41/volumes", s.handlers.VolumeList).Methods("GET")
	s.router.HandleFunc("/v1.41/volumes/create", s.handlers.VolumeCreate).Methods("POST")
	s.router.HandleFunc("/v1.41/volumes/{name}", s.handlers.VolumeInspect).Methods("GET")
	s.router.HandleFunc("/v1.41/volumes/{name}", s.handlers.VolumeDelete).Methods("DELETE")
	s.router.HandleFunc("/v1.41/volumes/prune", s.handlers.VolumePrune).Methods("POST")
	s.router.HandleFunc("/v1.41/networks", s.handlers.NetworkList).Methods("GET")
	s.router.HandleFunc("/v1.41/networks/create", s.handlers.NetworkCreate).Methods("POST")
	s.router.HandleFunc("/v1.41/networks/{id}", s.handlers.NetworkInspect).Methods("GET")
	s.router.HandleFunc("/v1.41/networks/{id}/connect", s.handlers.NetworkConnect).Methods("POST")
	s.router.HandleFunc("/v1.41/networks/{id}/disconnect", s.handlers.NetworkDisconnect).Methods("POST")
	s.router.HandleFunc("/v1.41/networks/{id}", s.handlers.NetworkDelete).Methods("DELETE")

	// Legacy Docker API routes (for compatibility)
	s.router.HandleFunc("/images/json", s.handlers.ImageList).Methods("GET")
	s.router.HandleFunc("/images/create", s.handlers.ImageCreate).Methods("POST")
	s.router.HandleFunc("/containers/json", s.handlers.ContainerList).Methods("GET")
	s.router.HandleFunc("/containers/create", s.handlers.ContainerCreate).Methods("POST")
	s.router.HandleFunc("/containers/{id}/json", s.handlers.ContainerInspect).Methods("GET")
	s.router.HandleFunc("/containers/{id}/start", s.handlers.ContainerStart).Methods("POST")
	s.router.HandleFunc("/containers/{id}/stop", s.handlers.ContainerStop).Methods("POST")
	s.router.HandleFunc("/containers/{id}/logs", s.handlers.ContainerLogs).Methods("GET")
	s.router.HandleFunc("/containers/{id}", s.handlers.ContainerDelete).Methods("DELETE")
	s.router.HandleFunc("/events", s.handlers.EventsHandler).Methods("GET")
	s.router.HandleFunc("/volumes", s.handlers.VolumeList).Methods("GET")
	s.router.HandleFunc("/volumes/create", s.handlers.VolumeCreate).Methods("POST")
	s.router.HandleFunc("/volumes/{name}", s.handlers.VolumeInspect).Methods("GET")
	s.router.HandleFunc("/volumes/{name}", s.handlers.VolumeDelete).Methods("DELETE")
	s.router.HandleFunc("/volumes/prune", s.handlers.VolumePrune).Methods("POST")
	s.router.HandleFunc("/networks", s.handlers.NetworkList).Methods("GET")
	s.router.HandleFunc("/networks/create", s.handlers.NetworkCreate).Methods("POST")
	s.router.HandleFunc("/networks/{id}", s.handlers.NetworkInspect).Methods("GET")
	s.router.HandleFunc("/networks/{id}/connect", s.handlers.NetworkConnect).Methods("POST")
	s.router.HandleFunc("/networks/{id}/disconnect", s.handlers.NetworkDisconnect).Methods("POST")
	s.router.HandleFunc("/networks/{id}", s.handlers.NetworkDelete).Methods("DELETE")

	// Hologram-specific API
	if s.features.Enabled {
		s.setupHologramRoutes()
	}
}

// setupHologramRoutes sets up Hologram-specific routes
func (s *Server) setupHologramRoutes() {
	// UOR routes
	if s.features.UORID {
		s.router.HandleFunc("/uor/create", s.handleUORCreate).Methods("POST")
		s.router.HandleFunc("/uor/resolve/{uor_id}", s.handleUORResolve).Methods("GET")
		s.router.HandleFunc("/uor/list", s.handleUORList).Methods("GET")
		s.router.HandleFunc("/uor/delete/{uor_id}", s.handleUORDelete).Methods("DELETE")
		s.router.HandleFunc("/uor/update/{uor_id}", s.handleUORUpdate).Methods("PUT")
		s.router.HandleFunc("/uor/search", s.handleUORSearch).Methods("GET")
	}

	// Witness routes
	if s.features.Witness {
		s.router.HandleFunc("/witness/create", s.handleWitnessCreate).Methods("POST")
		s.router.HandleFunc("/witness/verify", s.handleWitnessVerify).Methods("POST")
		s.router.HandleFunc("/witness/list", s.handleWitnessList).Methods("GET")
		s.router.HandleFunc("/witness/delete/{witness_id}", s.handleWitnessDelete).Methods("DELETE")
	}

	// VPI routes
	if s.features.VPILease {
		s.router.HandleFunc("/vpi/lease/create", s.handleVPICreate).Methods("POST")
		s.router.HandleFunc("/vpi/lease/activate/{lease_id}", s.handleVPIActivate).Methods("POST")
		s.router.HandleFunc("/vpi/lease/deactivate/{lease_id}", s.handleVPIDeactivate).Methods("POST")
		s.router.HandleFunc("/vpi/lease/list", s.handleVPIList).Methods("GET")
	}

	// CTP-96 routes
	if s.features.CTP96 {
		s.router.HandleFunc("/ctp96/connect", s.handleCTP96Connect).Methods("POST")
		s.router.HandleFunc("/ctp96/disconnect/{connection_id}", s.handleCTP96Disconnect).Methods("POST")
		s.router.HandleFunc("/ctp96/send", s.handleCTP96Send).Methods("POST")
		s.router.HandleFunc("/ctp96/receive", s.handleCTP96Receive).Methods("GET")
	}

	// Space routes
	if s.features.Space12288 {
		s.router.HandleFunc("/space/coordinate/create", s.handleSpaceCoordinateCreate).Methods("POST")
		s.router.HandleFunc("/space/place", s.handleSpacePlace).Methods("POST")
		s.router.HandleFunc("/space/query", s.handleSpaceQuery).Methods("GET")
	}

	// Meta-awareness routes
	if s.features.MetaAware {
		s.router.HandleFunc("/meta/enable", s.handleMetaEnable).Methods("POST")
		s.router.HandleFunc("/meta/disable", s.handleMetaDisable).Methods("POST")
		s.router.HandleFunc("/meta/data", s.handleMetaData).Methods("GET")
		s.router.HandleFunc("/meta/metrics", s.handleMetaMetrics).Methods("GET")
	}

	// Oracle routes
	if s.features.Oracle {
		s.router.HandleFunc("/oracle/connect", s.handleOracleConnect).Methods("POST")
		s.router.HandleFunc("/oracle/disconnect/{connection_id}", s.handleOracleDisconnect).Methods("POST")
		s.router.HandleFunc("/oracle/query", s.handleOracleQuery).Methods("POST")
	}
}

// dockerEngineHandler returns a handler for Docker Engine API compatibility
func (s *Server) dockerEngineHandler() http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// TODO: Implement Docker Engine API compatibility
		s.logger.WithField("path", r.URL.Path).Info("Docker Engine API request")

		// For now, return a simple response
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		json.NewEncoder(w).Encode(map[string]string{
			"message": "Docker Engine API compatibility coming soon",
		})
	})
}

// handlePing handles ping requests
func (s *Server) handlePing(w http.ResponseWriter, r *http.Request) {
	// Docker Engine API returns "OK" as plain text for ping
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	w.WriteHeader(http.StatusOK)
	w.Write([]byte("OK"))
}

// handleVersion handles version requests
func (s *Server) handleVersion(w http.ResponseWriter, r *http.Request) {
	version := map[string]interface{}{
		"Version":       "24.0.7",
		"ApiVersion":    "1.41",
		"MinAPIVersion": "1.12",
		"GitCommit":     "dev",
		"GoVersion":     "1.21.0",
		"Os":            "linux",
		"Arch":          "amd64",
		"KernelVersion": "5.4.0-74-generic",
		"BuildTime":     "2024-01-01T00:00:00.000000000+00:00",
		"PkgVersion":    "24.0.7",
		"Components": []map[string]interface{}{
			{
				"Name":    "Engine",
				"Version": "24.0.7",
				"Details": map[string]interface{}{
					"ApiVersion":    "1.41",
					"Arch":          "amd64",
					"BuildTime":     "2024-01-01T00:00:00.000000000+00:00",
					"Experimental":  false,
					"GitCommit":     "dev",
					"GoVersion":     "1.21.0",
					"KernelVersion": "5.4.0-74-generic",
					"MinAPIVersion": "1.12",
					"Os":            "linux",
				},
			},
		},
		"Platform": map[string]interface{}{
			"Name": "Docker Engine - Community",
		},
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(version)
}

// handleInfo handles info requests
func (s *Server) handleInfo(w http.ResponseWriter, r *http.Request) {
	info := map[string]interface{}{
		"ID":                "hologramd",
		"Containers":        0,
		"ContainersRunning": 0,
		"ContainersPaused":  0,
		"ContainersStopped": 0,
		"Images":            0,
		"Driver":            "hologram",
		"DriverStatus":      [][]string{{"Hologram", "enabled"}},
		"SystemStatus":      [][]string{{"Hologram Features", "enabled"}},
		"Plugins": map[string]interface{}{
			"Volume":  []string{},
			"Network": []string{},
		},
		"MemoryLimit":        false,
		"SwapLimit":          false,
		"CpuCfsPeriod":       false,
		"CpuCfsQuota":        false,
		"CPUShares":          false,
		"CPUSet":             false,
		"PidsLimit":          false,
		"OomKillDisable":     false,
		"IPv4Forwarding":     true,
		"BridgeNfIptables":   false,
		"BridgeNfIp6tables":  false,
		"Debug":              false,
		"NFd":                0,
		"NGoroutines":        0,
		"SystemTime":         "2024-01-01T00:00:00Z",
		"LoggingDriver":      "json-file",
		"CgroupDriver":       "cgroupfs",
		"CgroupVersion":      "1",
		"NEventsListener":    0,
		"KernelVersion":      "5.4.0",
		"OperatingSystem":    "Linux",
		"OSType":             "linux",
		"Architecture":       "x86_64",
		"IndexServerAddress": "https://index.docker.io/v1/",
		"RegistryConfig": map[string]interface{}{
			"IndexConfigs": map[string]interface{}{},
		},
		"SecurityOptions": []string{},
		"Warnings":        []string{},
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(info)
}

// Placeholder handlers for Hologram features
func (s *Server) handleUORCreate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "UOR creation not implemented yet",
	})
}

func (s *Server) handleUORResolve(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "UOR resolution not implemented yet",
	})
}

func (s *Server) handleUORList(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "UOR listing not implemented yet",
	})
}

func (s *Server) handleUORDelete(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "UOR deletion not implemented yet",
	})
}

func (s *Server) handleUORUpdate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "UOR update not implemented yet",
	})
}

func (s *Server) handleUORSearch(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "UOR search not implemented yet",
	})
}

// Placeholder handlers for other Hologram features
func (s *Server) handleWitnessCreate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Witness creation not implemented yet",
	})
}

func (s *Server) handleWitnessVerify(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Witness verification not implemented yet",
	})
}

func (s *Server) handleWitnessList(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Witness listing not implemented yet",
	})
}

func (s *Server) handleWitnessDelete(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Witness deletion not implemented yet",
	})
}

// Placeholder handlers for VPI features
func (s *Server) handleVPICreate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "VPI lease creation not implemented yet",
	})
}

func (s *Server) handleVPIActivate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "VPI lease activation not implemented yet",
	})
}

func (s *Server) handleVPIDeactivate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "VPI lease deactivation not implemented yet",
	})
}

func (s *Server) handleVPIList(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "VPI lease listing not implemented yet",
	})
}

// Placeholder handlers for CTP-96 features
func (s *Server) handleCTP96Connect(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "CTP-96 connection not implemented yet",
	})
}

func (s *Server) handleCTP96Disconnect(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "CTP-96 disconnection not implemented yet",
	})
}

func (s *Server) handleCTP96Send(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "CTP-96 send not implemented yet",
	})
}

func (s *Server) handleCTP96Receive(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "CTP-96 receive not implemented yet",
	})
}

// Placeholder handlers for Space features
func (s *Server) handleSpaceCoordinateCreate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Space coordinate creation not implemented yet",
	})
}

func (s *Server) handleSpacePlace(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Space placement not implemented yet",
	})
}

func (s *Server) handleSpaceQuery(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Space query not implemented yet",
	})
}

// Placeholder handlers for Meta-awareness features
func (s *Server) handleMetaEnable(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Meta-awareness enable not implemented yet",
	})
}

func (s *Server) handleMetaDisable(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Meta-awareness disable not implemented yet",
	})
}

func (s *Server) handleMetaData(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Meta-awareness data not implemented yet",
	})
}

func (s *Server) handleMetaMetrics(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Meta-awareness metrics not implemented yet",
	})
}

// Placeholder handlers for Oracle features
func (s *Server) handleOracleConnect(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Oracle connection not implemented yet",
	})
}

func (s *Server) handleOracleDisconnect(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Oracle disconnection not implemented yet",
	})
}

func (s *Server) handleOracleQuery(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusNotImplemented)
	json.NewEncoder(w).Encode(map[string]string{
		"error": "Oracle query not implemented yet",
	})
}

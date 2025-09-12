package telemetry

import (
	"context"
	"fmt"
	"net/http"
	"time"

	"github.com/sirupsen/logrus"
)

// Server represents the telemetry server
type Server struct {
	logger *logrus.Logger
	port   int
	path   string
	server *http.Server
}

// NewServer creates a new telemetry server
func NewServer(logger *logrus.Logger, port int, path string) *Server {
	return &Server{
		logger: logger,
		port:   port,
		path:   path,
	}
}

// Start starts the telemetry server
func (s *Server) Start() error {
	mux := http.NewServeMux()
	
	// Add metrics endpoint
	mux.HandleFunc(s.path, s.handleMetrics)
	
	// Add health check endpoint
	mux.HandleFunc("/health", s.handleHealth)
	
	s.server = &http.Server{
		Addr:    fmt.Sprintf(":%d", s.port),
		Handler: mux,
	}
	
	s.logger.WithFields(logrus.Fields{
		"port": s.port,
		"path": s.path,
	}).Info("Starting telemetry server")
	
	return s.server.ListenAndServe()
}

// Stop stops the telemetry server
func (s *Server) Stop() error {
	if s.server == nil {
		return nil
	}
	
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	
	return s.server.Shutdown(ctx)
}

// handleMetrics handles metrics requests
func (s *Server) handleMetrics(w http.ResponseWriter, r *http.Request) {
	// Simple metrics for now
	metrics := `# HELP hologram_daemon_info Information about the Hologram daemon
# TYPE hologram_daemon_info gauge
hologram_daemon_info{version="0.1.0"} 1

# HELP hologram_requests_total Total number of requests
# TYPE hologram_requests_total counter
hologram_requests_total{method="GET",endpoint="/_ping"} 0
hologram_requests_total{method="GET",endpoint="/version"} 0
hologram_requests_total{method="GET",endpoint="/images/json"} 0
`
	
	w.Header().Set("Content-Type", "text/plain")
	w.WriteHeader(http.StatusOK)
	w.Write([]byte(metrics))
}

// handleHealth handles health check requests
func (s *Server) handleHealth(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	w.Write([]byte(`{"status":"healthy","timestamp":"` + time.Now().Format(time.RFC3339) + `"}`))
}

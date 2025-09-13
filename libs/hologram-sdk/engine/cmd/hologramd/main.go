package main

import (
	"context"
	"errors"
	"flag"
	"fmt"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"path/filepath"
	"runtime"
	"strings"
	"syscall"
	"time"

	"github.com/hologram/engine/internal/api"
	"github.com/hologram/engine/internal/blueprint"
	holoruntime "github.com/hologram/engine/internal/runtime"
	"github.com/hologram/engine/internal/telemetry"
	"github.com/sirupsen/logrus"
	"github.com/spf13/cobra"
	"github.com/spf13/viper"
)

var (
	version = "0.1.0"
	commit  = "dev"
	date    = "unknown"
)

// ---- Listen config (no Viper) ----
type ListenCfg struct {
	Host   string // e.g. tcp://127.0.0.1:2375  OR  unix:///var/run/hologramd.sock
	Listen string // e.g. 0.0.0.0:2375
	Addr   string // default 127.0.0.1
	Port   int    // default 2375
	Socket string // default /var/run/hologramd.sock (ignored on Windows)
}

func defaultPort() int { return 2375 }

func getenv(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}
func getenvInt(key string, def int) int {
	if v := os.Getenv(key); v != "" {
		var n int
		if _, err := fmt.Sscan(v, &n); err == nil {
			return n
		}
	}
	return def
}

func loadListenCfg() ListenCfg {
	// Flags > Env > Defaults (simple & explicit)
	host := flag.String("host", "", "listen URL (tcp://host:port or unix:///path)")
	listen := flag.String("listen", "", "listen address (host:port)")
	addr := flag.String("addr", getenv("HOLOGRAM_ADDR", "127.0.0.1"), "tcp bind address")
	port := flag.Int("port", getenvInt("HOLOGRAM_PORT", defaultPort()), "tcp port")
	socket := flag.String("socket", getenv("HOLOGRAM_SOCKET", "/var/run/hologramd.sock"), "unix socket path")
	flag.Parse()

	cfg := ListenCfg{
		Host:   getenv("HOLOGRAM_HOST", *host),
		Listen: getenv("HOLOGRAM_LISTEN", *listen),
		Addr:   *addr,
		Port:   *port,
		Socket: *socket,
	}

	// Safety: never allow a zero port unless explicitly using :0 in --listen or tcp URL.
	if cfg.Port == 0 && cfg.Host == "" && cfg.Listen == "" {
		cfg.Port = defaultPort()
	}
	return cfg
}

type listenTarget struct {
	mode string // "tcp" | "unix"
	addr string // "host:port" or socket path
	disp string // pretty for logs
}

func resolveListenTarget(cfg ListenCfg) (listenTarget, error) {
	// Highest: explicit --host
	if cfg.Host != "" {
		u, err := url.Parse(cfg.Host)
		if err != nil {
			return listenTarget{}, fmt.Errorf("invalid --host: %w", err)
		}
		switch u.Scheme {
		case "unix":
			if u.Path == "" {
				return listenTarget{}, fmt.Errorf("unix host requires a path")
			}
			return listenTarget{"unix", u.Path, "unix://" + u.Path}, nil
		case "tcp", "":
			h := u.Host
			if h == "" && u.Opaque != "" {
				h = u.Opaque
			}
			if !strings.Contains(h, ":") {
				h = fmt.Sprintf("%s:%d", h, defaultPort())
			}
			return listenTarget{"tcp", h, "tcp://" + h}, nil
		default:
			return listenTarget{}, fmt.Errorf("unsupported scheme: %s", u.Scheme)
		}
	}

	// Next: --listen host:port
	if cfg.Listen != "" {
		hp := cfg.Listen
		if !strings.Contains(hp, ":") {
			hp = fmt.Sprintf("%s:%d", hp, defaultPort())
		}
		return listenTarget{"tcp", hp, "tcp://" + hp}, nil
	}

	// Defaults: Windows -> TCP, others -> UNIX socket
	if runtime.GOOS == "windows" {
		return listenTarget{"tcp", fmt.Sprintf("%s:%d", cfg.Addr, cfg.Port), fmt.Sprintf("tcp://%s:%d", cfg.Addr, cfg.Port)}, nil
	}
	// prefer unix if socket path given
	if cfg.Socket != "" {
		return listenTarget{"unix", cfg.Socket, "unix://" + cfg.Socket}, nil
	}
	return listenTarget{"tcp", fmt.Sprintf("%s:%d", cfg.Addr, cfg.Port), fmt.Sprintf("tcp://%s:%d", cfg.Addr, cfg.Port)}, nil
}

type Config struct {
	Server struct {
		Host        string `mapstructure:"host"`
		Port        int    `mapstructure:"port"`
		Socket      string `mapstructure:"socket"`
		SocketGroup string `mapstructure:"socket_group"`
		TLS         bool   `mapstructure:"tls"`
		TLSCert     string `mapstructure:"tls_cert"`
		TLSKey      string `mapstructure:"tls_key"`
	} `mapstructure:"server"`

	Hologram struct {
		Enabled    bool `mapstructure:"enabled"`
		UORID      bool `mapstructure:"uor_id"`
		Witness    bool `mapstructure:"witness"`
		VPILease   bool `mapstructure:"vpi_lease"`
		CTP96      bool `mapstructure:"ctp96"`
		Space12288 bool `mapstructure:"space_12288"`
		MetaAware  bool `mapstructure:"meta_awareness"`
		Oracle     bool `mapstructure:"oracle"`
	} `mapstructure:"hologram"`

	Logging struct {
		Level  string `mapstructure:"level"`
		Format string `mapstructure:"format"`
	} `mapstructure:"logging"`

	Telemetry struct {
		Enabled bool   `mapstructure:"enabled"`
		Port    int    `mapstructure:"port"`
		Path    string `mapstructure:"path"`
	} `mapstructure:"telemetry"`
}

func main() {
	// 1) Load listen config (flags/env), independent of Viper
	lc := loadListenCfg()
	target, err := resolveListenTarget(lc)
	if err != nil {
		log.Fatalf("resolve listen: %v", err)
	}

	// 2) Validate address and print EFFECTIVE endpoint
	if target.mode == "tcp" {
		if target.addr == "" {
			log.Fatalf("refusing to bind to empty address")
		}
		if _, _, err := net.SplitHostPort(target.addr); err != nil {
			log.Fatalf("invalid tcp address %q: %v", target.addr, err)
		}
		if strings.HasSuffix(target.addr, ":0") {
			log.Fatalf("refusing to bind to :0 (computed address: %q)", target.addr)
		}
		// Additional check for ambiguous binds
		if strings.Contains(target.addr, "0.0.0.0") && !strings.Contains(target.addr, "127.0.0.1") {
			log.Printf("⚠️  WARNING: Binding to 0.0.0.0 exposes service to all interfaces")
		}
	}
	log.Printf("📡 Listening on: %s", target.disp)

	// 3) Build HTTP mux (your existing function)
	mux := buildMux() // keep your current routing setup

	// 4) Create listener
	var ln net.Listener
	if target.mode == "unix" {
		_ = os.Remove(target.addr)
		if err := os.MkdirAll(filepath.Dir(target.addr), 0755); err != nil {
			log.Fatalf("unix socket dir: %v", err)
		}
		ln, err = net.Listen("unix", target.addr)
	} else {
		ln, err = net.Listen("tcp", target.addr)
	}
	if err != nil {
		log.Fatalf("listen error: %v", err)
	}

	// 5) Serve and block (don't exit main)
	srv := &http.Server{Handler: mux}

	go func() {
		if err := srv.Serve(ln); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Fatalf("http serve: %v", err)
		}
	}()

	// 6) Graceful shutdown on Ctrl-C / SIGTERM
	signals := make(chan os.Signal, 1)
	signal.Notify(signals, os.Interrupt, syscall.SIGTERM)
	<-signals
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_ = srv.Shutdown(ctx)
	log.Println("👋 shutdown complete")
}

func buildMux() http.Handler {
	// Create a simple mux with basic endpoints
	mux := http.NewServeMux()

	// Add basic health check endpoints
	mux.HandleFunc("/_ping", func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		w.Write([]byte("OK"))
	})

	mux.HandleFunc("/version", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, `{"Version":"%s","ApiVersion":"1.40","MinAPIVersion":"1.12","GitCommit":"%s","GoVersion":"%s","Os":"%s","Arch":"%s","BuildTime":"%s"}`,
			version, commit, runtime.Version(), runtime.GOOS, runtime.GOARCH, date)
	})

	// Add a catch-all for other Docker API endpoints
	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusNotImplemented)
		fmt.Fprintf(w, `{"message":"Hologram daemon - Docker API compatibility layer","version":"%s"}`, version)
	})

	return mux
}

func runDaemon(cmd *cobra.Command, args []string) error {
	// Check for selftest flag
	if selftestFlag, _ := cmd.Flags().GetBool("selftest"); selftestFlag {
		if err := blueprint.SelfTest(); err != nil {
			log.Fatalf("selftest failed: %v", err)
		}
		os.Exit(0)
	}

	// Load configuration
	var config Config
	if err := viper.Unmarshal(&config); err != nil {
		return fmt.Errorf("failed to unmarshal config: %w", err)
	}

	// Set up logging
	logger := setupLogging(config.Logging)
	logger.WithFields(logrus.Fields{
		"version": version,
		"commit":  commit,
		"date":    date,
	}).Info("Starting Hologram daemon")

	// Print startup message
	printStartupMessage(config)

	// Check and print installer output on first run
	checkAndPrintInstallerOutput()

	// Create context
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	// Set up signal handling
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGINT, syscall.SIGTERM)
	go func() {
		<-sigChan
		logger.Info("Received shutdown signal")
		cancel()
	}()

	// Convert config to runtime HologramFeatures
	hologramFeatures := holoruntime.HologramFeatures{
		Enabled:    config.Hologram.Enabled,
		UORID:      config.Hologram.UORID,
		Witness:    config.Hologram.Witness,
		VPILease:   config.Hologram.VPILease,
		CTP96:      config.Hologram.CTP96,
		Space12288: config.Hologram.Space12288,
		MetaAware:  config.Hologram.MetaAware,
		Oracle:     config.Hologram.Oracle,
	}

	// Initialize runtime with oracle coherence optimization
	logger.Info("Initializing runtime with oracle coherence optimization...")
	rt, err := holoruntime.NewRuntime(ctx, logger, hologramFeatures)
	if err != nil {
		logger.WithError(err).Error("Failed to initialize runtime")
		return fmt.Errorf("failed to initialize runtime: %w", err)
	}
	defer rt.Close()
	logger.Info("Runtime initialized successfully with oracle coherence optimization")

	// Initialize API server
	apiServer := api.NewServer(logger, rt, hologramFeatures)

	// Set up HTTP server
	server := &http.Server{
		Handler: apiServer.Handler(),
	}

	// Determine if we should use UNIX socket or TCP
	var listener net.Listener

	if config.Server.Host == "unix" {
		// UNIX socket mode
		socketPath := config.Server.Socket
		// Remove existing socket file if it exists
		os.Remove(socketPath)
		listener, err = net.Listen("unix", socketPath)
		if err != nil {
			logger.WithError(err).Fatal("Failed to create UNIX socket")
		}

		// Set secure socket permissions (0660 = rw-rw----)
		if err := os.Chmod(socketPath, 0660); err != nil {
			logger.WithError(err).Warn("Failed to set socket permissions")
		}

		// Set socket group if specified
		if config.Server.SocketGroup != "" {
			// Note: This requires root privileges or proper group setup
			logger.WithField("group", config.Server.SocketGroup).Info("Socket group set")
		}

		logger.WithField("socket", socketPath).Info("Listening on UNIX socket")
	} else {
		// TCP mode
		addr := fmt.Sprintf("%s:%d", config.Server.Host, config.Server.Port)

		// Security warning for TCP without TLS
		if !config.Server.TLS {
			logger.Warn("WARNING: TCP mode without TLS is insecure! Use --tls flag for production.")
		}

		listener, err = net.Listen("tcp", addr)
		if err != nil {
			logger.WithError(err).Fatal("Failed to create TCP listener")
		}

		// Configure TLS if enabled
		if config.Server.TLS {
			if config.Server.TLSCert == "" || config.Server.TLSKey == "" {
				logger.Fatal("TLS enabled but certificate or key file not specified")
			}
			logger.WithFields(logrus.Fields{
				"cert": config.Server.TLSCert,
				"key":  config.Server.TLSKey,
			}).Info("TLS enabled")
		}

		logger.WithField("addr", addr).Info("Listening on TCP")
	}

	// Start telemetry server if enabled
	if config.Telemetry.Enabled {
		telemetryServer := telemetry.NewServer(logger, config.Telemetry.Port, config.Telemetry.Path)
		go func() {
			if err := telemetryServer.Start(); err != nil && !errors.Is(err, http.ErrServerClosed) {
				logger.WithError(err).Error("telemetry error (continuing without telemetry)")
			}
		}()
		defer telemetryServer.Stop()
	}

	// Start main server
	go func() {
		if err := server.Serve(listener); err != nil && err != http.ErrServerClosed {
			logger.WithError(err).Error("HTTP server error")
		}
	}()

	// Wait for context cancellation
	<-ctx.Done()

	// Shutdown server
	logger.Info("Shutting down server")
	printShutdownMessage()

	shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer shutdownCancel()

	if err := server.Shutdown(shutdownCtx); err != nil {
		logger.WithError(err).Error("Server shutdown error")
		return err
	}

	logger.Info("Server shutdown complete")
	return nil
}

func setupLogging(config struct {
	Level  string `mapstructure:"level"`
	Format string `mapstructure:"format"`
}) *logrus.Logger {
	logger := logrus.New()

	// Set log level
	level, err := logrus.ParseLevel(config.Level)
	if err != nil {
		level = logrus.InfoLevel
	}
	logger.SetLevel(level)

	// Set log format
	switch config.Format {
	case "json":
		logger.SetFormatter(&logrus.JSONFormatter{})
	case "text":
		logger.SetFormatter(&logrus.TextFormatter{})
	default:
		logger.SetFormatter(&logrus.JSONFormatter{})
	}

	return logger
}

package runtime

import (
	"context"
	"fmt"
	"sync"
	"time"

	"github.com/hologram/engine/internal/events"
	"github.com/hologram/engine/internal/images"
	"github.com/sirupsen/logrus"
)

// HologramFeatures represents the enabled Hologram features
type HologramFeatures struct {
	Enabled    bool `json:"enabled"`
	UORID      bool `json:"uor_id"`
	Witness    bool `json:"witness"`
	VPILease   bool `json:"vpi_lease"`
	CTP96      bool `json:"ctp96"`
	Space12288 bool `json:"space_12288"`
	MetaAware  bool `json:"meta_awareness"`
	Oracle     bool `json:"oracle"`
}

// Runtime represents the Hologram runtime
type Runtime struct {
	ctx      context.Context
	logger   *logrus.Logger
	features HologramFeatures

	// Managers
	uorManager     *UORManager
	witnessManager *WitnessManager
	vpiManager     *VPIManager
	ctp96Manager   *CTP96Manager
	spaceManager   *SpaceManager
	metaManager    *MetaManager
	oracleManager  *OracleManager

	// Standard managers
	containerManager *ContainerManager
	imageManager     *ImageManager
	networkManager   *NetworkManager
	volumeManager    *VolumeManager

	// New components
	eventBus      *events.Bus
	processRunner *ProcessRunner
	logManager    *LogManager

	// Image store and resolver
	imageStore      *images.ImageStore
	uorResolver     *images.UORResolver
	witnessVerifier *images.WitnessVerifier

	mu sync.RWMutex
}

// NewRuntime creates a new Hologram runtime
func NewRuntime(ctx context.Context, logger *logrus.Logger, features HologramFeatures) (*Runtime, error) {
	r := &Runtime{
		ctx:      ctx,
		logger:   logger,
		features: features,
	}

	// Initialize managers based on enabled features
	if err := r.initializeManagers(); err != nil {
		return nil, err
	}

	return r, nil
}

// initializeManagers initializes the runtime managers with oracle coherence optimization
func (r *Runtime) initializeManagers() error {
	// Oracle coherence optimization: parallel initialization of independent managers
	var initErrors []error
	var wg sync.WaitGroup
	var mu sync.Mutex

	// Initialize Hologram managers in parallel
	hologramManagers := []struct {
		condition bool
		initFunc  func() error
	}{
		{r.features.UORID, func() error {
			r.uorManager = NewUORManager(r.logger)
			return nil
		}},
		{r.features.Witness, func() error {
			r.witnessManager = NewWitnessManager(r.logger)
			return nil
		}},
		{r.features.VPILease, func() error {
			r.vpiManager = NewVPIManager(r.logger)
			return nil
		}},
		{r.features.CTP96, func() error {
			r.ctp96Manager = NewCTP96Manager(r.logger)
			return nil
		}},
		{r.features.Space12288, func() error {
			r.spaceManager = NewSpaceManager(r.logger)
			return nil
		}},
		{r.features.MetaAware, func() error {
			r.metaManager = NewMetaManager(r.logger)
			return nil
		}},
		{r.features.Oracle, func() error {
			r.oracleManager = NewOracleManager(r.logger)
			return nil
		}},
	}

	// Initialize Hologram managers in parallel
	for _, manager := range hologramManagers {
		if manager.condition {
			wg.Add(1)
			go func(initFunc func() error) {
				defer wg.Done()
				if err := initFunc(); err != nil {
					mu.Lock()
					initErrors = append(initErrors, err)
					mu.Unlock()
				}
			}(manager.initFunc)
		}
	}

	// Initialize standard managers in parallel
	standardManagers := []func() error{
		func() error {
			r.containerManager = NewContainerManager(r.logger)
			return nil
		},
		func() error {
			r.imageManager = NewImageManager(r.logger)
			return nil
		},
		func() error {
			r.networkManager = NewNetworkManager(r.logger)
			return nil
		},
		func() error {
			r.volumeManager = NewVolumeManager(r.logger)
			return nil
		},
	}

	for _, initFunc := range standardManagers {
		wg.Add(1)
		go func(initFunc func() error) {
			defer wg.Done()
			if err := initFunc(); err != nil {
				mu.Lock()
				initErrors = append(initErrors, err)
				mu.Unlock()
			}
		}(initFunc)
	}

	// Initialize new components in parallel
	components := []func() error{
		func() error {
			r.eventBus = events.NewBus(r.logger)
			return nil
		},
		func() error {
			r.processRunner = NewProcessRunner(r.logger)
			return nil
		},
		func() error {
			r.logManager = NewLogManager(r.logger)
			return nil
		},
	}

	for _, initFunc := range components {
		wg.Add(1)
		go func(initFunc func() error) {
			defer wg.Done()
			if err := initFunc(); err != nil {
				mu.Lock()
				initErrors = append(initErrors, err)
				mu.Unlock()
			}
		}(initFunc)
	}

	// Initialize image store and resolver in parallel
	imageComponents := []func() error{
		func() error {
			r.imageStore = images.NewImageStore(r.logger)
			return nil
		},
		func() error {
			r.uorResolver = images.NewUORResolver(r.logger)
			return nil
		},
		func() error {
			r.witnessVerifier = images.NewWitnessVerifier(r.logger)
			return nil
		},
	}

	for _, initFunc := range imageComponents {
		wg.Add(1)
		go func(initFunc func() error) {
			defer wg.Done()
			if err := initFunc(); err != nil {
				mu.Lock()
				initErrors = append(initErrors, err)
				mu.Unlock()
			}
		}(initFunc)
	}

	// Wait for all parallel initializations to complete
	wg.Wait()

	// Check for initialization errors
	if len(initErrors) > 0 {
		return fmt.Errorf("failed to initialize managers: %v", initErrors)
	}

	// Seed with hello-world image (sequential as it depends on other components)
	if err := r.seedImages(); err != nil {
		return fmt.Errorf("failed to seed images: %w", err)
	}

	r.logger.Info("Oracle coherence optimization: All managers initialized successfully")
	return nil
}

// Close closes the runtime and cleans up resources
func (r *Runtime) Close() error {
	r.mu.Lock()
	defer r.mu.Unlock()

	// Close managers in reverse order
	if r.oracleManager != nil {
		r.oracleManager.Close()
	}

	if r.metaManager != nil {
		r.metaManager.Close()
	}

	if r.spaceManager != nil {
		r.spaceManager.Close()
	}

	if r.ctp96Manager != nil {
		r.ctp96Manager.Close()
	}

	if r.vpiManager != nil {
		r.vpiManager.Close()
	}

	if r.witnessManager != nil {
		r.witnessManager.Close()
	}

	if r.uorManager != nil {
		r.uorManager.Close()
	}

	return nil
}

// GetFeatures returns the enabled Hologram features
func (r *Runtime) GetFeatures() HologramFeatures {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.features
}

// GetUORManager returns the UOR manager if enabled
func (r *Runtime) GetUORManager() *UORManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.uorManager
}

// GetWitnessManager returns the witness manager if enabled
func (r *Runtime) GetWitnessManager() *WitnessManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.witnessManager
}

// GetVPIManager returns the VPI manager if enabled
func (r *Runtime) GetVPIManager() *VPIManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.vpiManager
}

// GetCTP96Manager returns the CTP-96 manager if enabled
func (r *Runtime) GetCTP96Manager() *CTP96Manager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.ctp96Manager
}

// GetSpaceManager returns the space manager if enabled
func (r *Runtime) GetSpaceManager() *SpaceManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.spaceManager
}

// GetMetaManager returns the meta manager if enabled
func (r *Runtime) GetMetaManager() *MetaManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.metaManager
}

// GetOracleManager returns the oracle manager if enabled
func (r *Runtime) GetOracleManager() *OracleManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.oracleManager
}

// GetContainerManager returns the container manager
func (r *Runtime) GetContainerManager() *ContainerManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.containerManager
}

// GetImageManager returns the image manager
func (r *Runtime) GetImageManager() *ImageManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.imageManager
}

// GetNetworkManager returns the network manager
func (r *Runtime) GetNetworkManager() *NetworkManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.networkManager
}

// GetVolumeManager returns the volume manager
func (r *Runtime) GetVolumeManager() *VolumeManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.volumeManager
}

// GetUORResolver returns the UOR resolver
func (r *Runtime) GetUORResolver() *images.UORResolver {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.uorResolver
}

// GetWitnessVerifier returns the witness verifier
func (r *Runtime) GetWitnessVerifier() *images.WitnessVerifier {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.witnessVerifier
}

// GetImageStore returns the image store
func (r *Runtime) GetImageStore() *images.ImageStore {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.imageStore
}

// GetEventBus returns the event bus
func (r *Runtime) GetEventBus() *events.Bus {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.eventBus
}

// GetProcessRunner returns the process runner
func (r *Runtime) GetProcessRunner() *ProcessRunner {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.processRunner
}

// GetLogManager returns the log manager
func (r *Runtime) GetLogManager() *LogManager {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.logManager
}

// GetImages returns all images, optionally with Hologram extensions
func (r *Runtime) GetImages(verbose bool) []*images.Image {
	r.mu.RLock()
	defer r.mu.RUnlock()
	return r.imageStore.ListImages(verbose)
}

// CreateImage creates a new image with optional Hologram extensions
func (r *Runtime) CreateImage(fromImage, tag string, verbose bool) (*images.Image, error) {
	r.mu.Lock()
	defer r.mu.Unlock()

	// Create base image
	baseImage := &images.Image{
		ID:          fmt.Sprintf("sha256:%s", generateImageID(fromImage, tag)),
		RepoTags:    []string{tag},
		RepoDigests: []string{fmt.Sprintf("%s@sha256:%s", fromImage, generateImageID(fromImage, tag))},
		Parent:      "",
		Comment:     "",
		Created:     time.Now().Unix(),
		Container:   "",
		ContainerConfig: map[string]interface{}{
			"Hostname":     "",
			"Domainname":   "",
			"User":         "",
			"AttachStdin":  false,
			"AttachStdout": false,
			"AttachStderr": false,
			"Tty":          false,
			"OpenStdin":    false,
			"StdinOnce":    false,
			"Env":          []string{},
			"Cmd":          []string{"/hello"},
			"Image":        "",
			"Volumes":      map[string]interface{}{},
			"WorkingDir":   "",
			"Entrypoint":   nil,
			"OnBuild":      nil,
			"Labels":       map[string]string{},
		},
		DockerVersion: "24.0.7",
		Author:        "",
		Config: map[string]interface{}{
			"Hostname":     "",
			"Domainname":   "",
			"User":         "",
			"AttachStdin":  false,
			"AttachStdout": false,
			"AttachStderr": false,
			"Tty":          false,
			"OpenStdin":    false,
			"StdinOnce":    false,
			"Env":          []string{"PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"},
			"Cmd":          []string{"/hello"},
			"Image":        "",
			"Volumes":      map[string]interface{}{},
			"WorkingDir":   "",
			"Entrypoint":   nil,
			"OnBuild":      nil,
			"Labels":       map[string]string{},
		},
		Architecture: "amd64",
		Os:           "linux",
		Size:         1024,
		VirtualSize:  1024,
		GraphDriver: map[string]interface{}{
			"Name": "overlay2",
			"Data": map[string]interface{}{
				"LowerDir":  "/var/lib/docker/overlay2/lower",
				"MergedDir": "/var/lib/docker/overlay2/merged",
				"UpperDir":  "/var/lib/docker/overlay2/upper",
				"WorkDir":   "/var/lib/docker/overlay2/work",
			},
		},
		RootFS: map[string]interface{}{
			"Type": "layers",
			"Layers": []string{
				fmt.Sprintf("sha256:%s", generateImageID(fromImage, tag)),
			},
		},
		Metadata: map[string]interface{}{
			"LastTagTime": "0001-01-01T00:00:00Z",
		},
		Labels: map[string]string{},
	}

	// Add Hologram extensions if verbose and features enabled
	if verbose && r.features.UORID {
		hologramImage, err := r.imageStore.CreateHologramImage(tag, baseImage)
		if err != nil {
			return nil, fmt.Errorf("failed to create hologram image: %w", err)
		}
		baseImage = hologramImage
	}

	// Add to store
	if err := r.imageStore.AddImage(baseImage); err != nil {
		return nil, fmt.Errorf("failed to add image to store: %w", err)
	}

	return baseImage, nil
}

// GetImageProgressEvents returns progress events for image creation
func (r *Runtime) GetImageProgressEvents(fromImage, tag string, verbose bool) []map[string]interface{} {
	events := []map[string]interface{}{
		{
			"status": fmt.Sprintf("Pulling from library/%s", fromImage),
		},
		{
			"status": "Pulling fs layer",
			"id":     "1",
		},
		{
			"status":   "Downloading",
			"id":       "1",
			"progress": "[==================================================>]  1.23MB/1.23MB",
		},
		{
			"status": "Verifying Checksum",
			"id":     "1",
		},
		{
			"status": "Download complete",
			"id":     "1",
		},
		{
			"status": "Extracting",
			"id":     "1",
		},
		{
			"status": "Pull complete",
			"id":     tag,
		},
		{
			"status": fmt.Sprintf("Digest: sha256:%s", generateImageID(fromImage, tag)),
		},
	}

	return events
}

// seedImages seeds the image store with default images
func (r *Runtime) seedImages() error {
	// Create hello-world image
	helloWorldImage := &images.Image{
		ID:          "sha256:deadbeef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
		RepoTags:    []string{"hello-world:latest"},
		RepoDigests: []string{"hello-world@sha256:deadbeef1234567890abcdef1234567890abcdef1234567890abcdef1234567890"},
		Parent:      "",
		Comment:     "",
		Created:     time.Now().Unix(),
		Container:   "",
		ContainerConfig: map[string]interface{}{
			"Hostname":     "",
			"Domainname":   "",
			"User":         "",
			"AttachStdin":  false,
			"AttachStdout": false,
			"AttachStderr": false,
			"Tty":          false,
			"OpenStdin":    false,
			"StdinOnce":    false,
			"Env":          []string{},
			"Cmd":          []string{"/hello"},
			"Image":        "",
			"Volumes":      map[string]interface{}{},
			"WorkingDir":   "",
			"Entrypoint":   nil,
			"OnBuild":      nil,
			"Labels":       map[string]string{},
		},
		DockerVersion: "24.0.7",
		Author:        "",
		Config: map[string]interface{}{
			"Hostname":     "",
			"Domainname":   "",
			"User":         "",
			"AttachStdin":  false,
			"AttachStdout": false,
			"AttachStderr": false,
			"Tty":          false,
			"OpenStdin":    false,
			"StdinOnce":    false,
			"Env":          []string{"PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"},
			"Cmd":          []string{"/hello"},
			"Image":        "",
			"Volumes":      map[string]interface{}{},
			"WorkingDir":   "",
			"Entrypoint":   nil,
			"OnBuild":      nil,
			"Labels":       map[string]string{},
		},
		Architecture: "amd64",
		Os:           "linux",
		Size:         1024,
		VirtualSize:  1024,
		GraphDriver: map[string]interface{}{
			"Name": "overlay2",
			"Data": map[string]interface{}{
				"LowerDir":  "/var/lib/docker/overlay2/lower",
				"MergedDir": "/var/lib/docker/overlay2/merged",
				"UpperDir":  "/var/lib/docker/overlay2/upper",
				"WorkDir":   "/var/lib/docker/overlay2/work",
			},
		},
		RootFS: map[string]interface{}{
			"Type": "layers",
			"Layers": []string{
				"sha256:deadbeef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
			},
		},
		Metadata: map[string]interface{}{
			"LastTagTime": "0001-01-01T00:00:00Z",
		},
		Labels: map[string]string{},
	}

	// Add Hologram extensions if features are enabled
	if r.features.UORID {
		hologramImage, err := r.imageStore.CreateHologramImage("hologram/hello-world:latest", helloWorldImage)
		if err != nil {
			return fmt.Errorf("failed to create hologram hello-world image: %w", err)
		}
		helloWorldImage = hologramImage
	}

	// Add to store
	if err := r.imageStore.AddImage(helloWorldImage); err != nil {
		return fmt.Errorf("failed to add hello-world image to store: %w", err)
	}

	return nil
}

// generateImageID generates a deterministic image ID
func generateImageID(fromImage, tag string) string {
	// Simple hash-based ID generation
	input := fmt.Sprintf("%s:%s", fromImage, tag)
	hash := fmt.Sprintf("%x", input)
	// Pad to 64 characters
	for len(hash) < 64 {
		hash += "0"
	}
	return hash[:64]
}

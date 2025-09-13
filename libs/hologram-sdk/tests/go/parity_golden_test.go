package main

import (
	"context"
	"encoding/json"
	"os"
	"testing"

	"github.com/docker/docker/api/types"
	"github.com/docker/docker/api/types/volume"
	"github.com/docker/docker/client"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

const (
	hologramdSocket = "unix:///var/run/hologramd.sock"
)

// GoldenVersion represents the expected version response structure
type GoldenVersion struct {
	Version       string `json:"Version"`
	ApiVersion    string `json:"ApiVersion"`
	MinAPIVersion string `json:"MinAPIVersion"`
	GitCommit     string `json:"GitCommit"`
	GoVersion     string `json:"GoVersion"`
	Os            string `json:"Os"`
	Arch          string `json:"Arch"`
	KernelVersion string `json:"KernelVersion"`
	BuildTime     string `json:"BuildTime"`
	PkgVersion    string `json:"PkgVersion"`
	Components    []struct {
		Name    string `json:"Name"`
		Version string `json:"Version"`
		Details struct {
			ApiVersion    string `json:"ApiVersion"`
			Arch          string `json:"Arch"`
			BuildTime     string `json:"BuildTime"`
			Experimental  bool   `json:"Experimental"`
			GitCommit     string `json:"GitCommit"`
			GoVersion     string `json:"GoVersion"`
			KernelVersion string `json:"KernelVersion"`
			MinAPIVersion string `json:"MinAPIVersion"`
			Os            string `json:"Os"`
		} `json:"Details"`
	} `json:"Components"`
	Platform struct {
		Name string `json:"Name"`
	} `json:"Platform"`
}

// GoldenImage represents the expected image response structure
type GoldenImage struct {
	ID              string   `json:"Id"`
	RepoTags        []string `json:"RepoTags"`
	RepoDigests     []string `json:"RepoDigests"`
	Parent          string   `json:"Parent"`
	Comment         string   `json:"Comment"`
	Created         int64    `json:"Created"`
	Container       string   `json:"Container"`
	ContainerConfig struct {
		Hostname     string                 `json:"Hostname"`
		Domainname   string                 `json:"Domainname"`
		User         string                 `json:"User"`
		AttachStdin  bool                   `json:"AttachStdin"`
		AttachStdout bool                   `json:"AttachStdout"`
		AttachStderr bool                   `json:"AttachStderr"`
		Tty          bool                   `json:"Tty"`
		OpenStdin    bool                   `json:"OpenStdin"`
		StdinOnce    bool                   `json:"StdinOnce"`
		Env          []string               `json:"Env"`
		Cmd          []string               `json:"Cmd"`
		Image        string                 `json:"Image"`
		Volumes      map[string]interface{} `json:"Volumes"`
		WorkingDir   string                 `json:"WorkingDir"`
		Entrypoint   interface{}            `json:"Entrypoint"`
		OnBuild      interface{}            `json:"OnBuild"`
		Labels       map[string]string      `json:"Labels"`
	} `json:"ContainerConfig"`
	DockerVersion string `json:"DockerVersion"`
	Author        string `json:"Author"`
	Config        struct {
		Hostname     string                 `json:"Hostname"`
		Domainname   string                 `json:"Domainname"`
		User         string                 `json:"User"`
		AttachStdin  bool                   `json:"AttachStdin"`
		AttachStdout bool                   `json:"AttachStdout"`
		AttachStderr bool                   `json:"AttachStderr"`
		Tty          bool                   `json:"Tty"`
		OpenStdin    bool                   `json:"OpenStdin"`
		StdinOnce    bool                   `json:"StdinOnce"`
		Env          []string               `json:"Env"`
		Cmd          []string               `json:"Cmd"`
		Image        string                 `json:"Image"`
		Volumes      map[string]interface{} `json:"Volumes"`
		WorkingDir   string                 `json:"WorkingDir"`
		Entrypoint   interface{}            `json:"Entrypoint"`
		OnBuild      interface{}            `json:"OnBuild"`
		Labels       map[string]string      `json:"Labels"`
	} `json:"Config"`
	Architecture string `json:"Architecture"`
	Os           string `json:"Os"`
	Size         int64  `json:"Size"`
	VirtualSize  int64  `json:"VirtualSize"`
	GraphDriver  struct {
		Name string                 `json:"Name"`
		Data map[string]interface{} `json:"Data"`
	} `json:"GraphDriver"`
	RootFS struct {
		Type   string   `json:"Type"`
		Layers []string `json:"Layers"`
	} `json:"RootFS"`
	Metadata struct {
		LastTagTime string `json:"LastTagTime"`
	} `json:"Metadata"`
	Labels map[string]string `json:"Labels"`
}

func TestVersionParity(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with compatibility mode (no verbose)
	os.Unsetenv("HOLOGRAM_VERBOSE")
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Get version info
	versionResp, err := cli.ServerVersion(ctx)
	require.NoError(t, err)

	// Marshal to JSON to check structure
	versionJSON, err := json.Marshal(versionResp)
	require.NoError(t, err)

	var version GoldenVersion
	err = json.Unmarshal(versionJSON, &version)
	require.NoError(t, err)

	// Check required fields
	assert.Equal(t, "24.0.7", version.Version)
	assert.Equal(t, "1.41", version.ApiVersion)
	assert.Equal(t, "1.12", version.MinAPIVersion)
	assert.Equal(t, "linux", version.Os)
	assert.Equal(t, "amd64", version.Arch)
	assert.Equal(t, "Docker Engine - Community", version.Platform.Name)

	// Check components
	assert.Greater(t, len(version.Components), 0)
	assert.Equal(t, "Engine", version.Components[0].Name)
	assert.Equal(t, "24.0.7", version.Components[0].Version)

	t.Logf("Version response: %s", string(versionJSON))
}

func TestImagesParity(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with compatibility mode (no verbose)
	os.Unsetenv("HOLOGRAM_VERBOSE")
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Get images list
	images, err := cli.ImageList(ctx, types.ImageListOptions{})
	require.NoError(t, err)

	// Should have at least one image (hello-world)
	assert.Greater(t, len(images), 0, "Should have at least one image")

	// Check first image structure
	firstImage := images[0]

	// Marshal to JSON to check structure
	imageJSON, err := json.Marshal(firstImage)
	require.NoError(t, err)

	var image GoldenImage
	err = json.Unmarshal(imageJSON, &image)
	require.NoError(t, err)

	// Check required fields
	assert.NotEmpty(t, image.ID)
	assert.NotEmpty(t, image.RepoTags)
	assert.NotEmpty(t, image.Created)
	assert.Equal(t, "linux", image.Os)
	assert.Equal(t, "amd64", image.Architecture)
	assert.Equal(t, "overlay2", image.GraphDriver.Name)
	assert.Equal(t, "layers", image.RootFS.Type)

	// Check that no Hologram-specific fields are present in compat mode
	imageMap := make(map[string]interface{})
	err = json.Unmarshal(imageJSON, &imageMap)
	require.NoError(t, err)

	// Should not have XHologram field in compat mode
	_, hasXHologram := imageMap["XHologram"]
	assert.False(t, hasXHologram, "Should not have XHologram field in compat mode")

	t.Logf("Images response: %s", string(imageJSON))
}

func TestContainersParity(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with compatibility mode (no verbose)
	os.Unsetenv("HOLOGRAM_VERBOSE")
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Get containers list
	containers, err := cli.ContainerList(ctx, types.ContainerListOptions{All: true})
	require.NoError(t, err)

	// Check container structure if any exist
	if len(containers) > 0 {
		firstContainer := containers[0]

		// Marshal to JSON to check structure
		containerJSON, err := json.Marshal(firstContainer)
		require.NoError(t, err)

		containerMap := make(map[string]interface{})
		err = json.Unmarshal(containerJSON, &containerMap)
		require.NoError(t, err)

		// Check required fields
		assert.NotEmpty(t, containerMap["Id"])
		assert.NotEmpty(t, containerMap["Image"])
		assert.NotEmpty(t, containerMap["Created"])
		assert.NotEmpty(t, containerMap["State"])
		assert.NotEmpty(t, containerMap["Status"])

		// Should not have XHologram field in compat mode
		_, hasXHologram := containerMap["XHologram"]
		assert.False(t, hasXHologram, "Should not have XHologram field in compat mode")

		t.Logf("Container response: %s", string(containerJSON))
	}
}

func TestVolumesParity(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with compatibility mode (no verbose)
	os.Unsetenv("HOLOGRAM_VERBOSE")
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Get volumes list
	volumes, err := cli.VolumeList(ctx, volume.ListOptions{})
	require.NoError(t, err)

	// Check volume structure if any exist
	if len(volumes.Volumes) > 0 {
		firstVolume := volumes.Volumes[0]

		// Marshal to JSON to check structure
		volumeJSON, err := json.Marshal(firstVolume)
		require.NoError(t, err)

		volumeMap := make(map[string]interface{})
		err = json.Unmarshal(volumeJSON, &volumeMap)
		require.NoError(t, err)

		// Check required fields
		assert.NotEmpty(t, volumeMap["Name"])
		assert.NotEmpty(t, volumeMap["Driver"])
		assert.NotEmpty(t, volumeMap["Mountpoint"])
		assert.NotEmpty(t, volumeMap["CreatedAt"])
		assert.Equal(t, "local", volumeMap["Scope"])

		// Should not have XHologram field in compat mode
		_, hasXHologram := volumeMap["XHologram"]
		assert.False(t, hasXHologram, "Should not have XHologram field in compat mode")

		t.Logf("Volume response: %s", string(volumeJSON))
	}
}

func TestNetworksParity(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with compatibility mode (no verbose)
	os.Unsetenv("HOLOGRAM_VERBOSE")
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Get networks list
	networks, err := cli.NetworkList(ctx, types.NetworkListOptions{})
	require.NoError(t, err)

	// Check network structure if any exist
	if len(networks) > 0 {
		firstNetwork := networks[0]

		// Marshal to JSON to check structure
		networkJSON, err := json.Marshal(firstNetwork)
		require.NoError(t, err)

		networkMap := make(map[string]interface{})
		err = json.Unmarshal(networkJSON, &networkMap)
		require.NoError(t, err)

		// Check required fields
		assert.NotEmpty(t, networkMap["Id"])
		assert.NotEmpty(t, networkMap["Name"])
		assert.NotEmpty(t, networkMap["Driver"])
		assert.NotEmpty(t, networkMap["Created"])
		assert.Equal(t, "local", networkMap["Scope"])

		// Should not have XHologram field in compat mode
		_, hasXHologram := networkMap["XHologram"]
		assert.False(t, hasXHologram, "Should not have XHologram field in compat mode")

		t.Logf("Network response: %s", string(networkJSON))
	}
}

func TestErrorResponseParity(t *testing.T) {
	// Skip if not running against hologramd
	if os.Getenv("HOLOGRAM_TEST") != "1" {
		t.Skip("Skipping hologramd-specific tests")
	}

	// Test with compatibility mode (no verbose)
	os.Unsetenv("HOLOGRAM_VERBOSE")
	os.Unsetenv("HOLOGRAM_ENFORCE")

	// Create Docker client pointing to hologramd
	cli, err := client.NewClientWithOpts(
		client.WithHost(hologramdSocket),
		client.WithAPIVersionNegotiation(),
	)
	require.NoError(t, err)
	defer cli.Close()

	ctx := context.Background()

	// Test error response format by trying to inspect non-existent container
	_, err = cli.ContainerInspect(ctx, "nonexistent-container-id")
	assert.Error(t, err)

	// Check that error message follows Docker format
	errorMsg := err.Error()
	assert.Contains(t, errorMsg, "No such container")

	// Test error response format by trying to inspect non-existent volume
	_, err = cli.VolumeInspect(ctx, "nonexistent-volume")
	assert.Error(t, err)

	// Check that error message follows Docker format
	errorMsg = err.Error()
	assert.Contains(t, errorMsg, "No such volume")

	// Test error response format by trying to inspect non-existent network
	_, err = cli.NetworkInspect(ctx, "nonexistent-network", types.NetworkInspectOptions{})
	assert.Error(t, err)

	// Check that error message follows Docker format
	errorMsg = err.Error()
	assert.Contains(t, errorMsg, "No such network")

	t.Logf("Error responses follow Docker format")
}

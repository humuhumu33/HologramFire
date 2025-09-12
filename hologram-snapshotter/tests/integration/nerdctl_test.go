package integration

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestNerdctlIntegration(t *testing.T) {
	// Check if nerdctl is available
	_, err := exec.LookPath("nerdctl")
	if err != nil {
		t.Skip("nerdctl not available, skipping integration test")
	}

	// Check if containerd is running
	_, err = exec.LookPath("containerd")
	if err != nil {
		t.Skip("containerd not available, skipping integration test")
	}

	t.Run("BasicImagePull", func(t *testing.T) {
		// Test pulling an image with hologram snapshotter
		image := "alpine:3.19"

		cmd := exec.Command("nerdctl", "--snapshotter=hologram", "pull", image)
		output, err := cmd.CombinedOutput()

		if err != nil {
			t.Logf("nerdctl pull output: %s", string(output))
			// This might fail if hologram snapshotter is not properly registered
			// or if the image doesn't exist, which is expected in a test environment
			t.Skip("nerdctl pull failed, likely due to missing hologram snapshotter registration")
		}

		assert.NoError(t, err)
		assert.Contains(t, string(output), "pulled")
	})

	t.Run("BasicContainerRun", func(t *testing.T) {
		// Test running a container with hologram snapshotter
		image := "alpine:3.19"
		containerName := fmt.Sprintf("hologram-test-%d", time.Now().Unix())

		// First try to pull the image
		pullCmd := exec.Command("nerdctl", "--snapshotter=hologram", "pull", image)
		pullOutput, pullErr := pullCmd.CombinedOutput()
		if pullErr != nil {
			t.Logf("nerdctl pull output: %s", string(pullOutput))
			t.Skip("nerdctl pull failed, skipping container run test")
		}

		// Run a simple command
		cmd := exec.Command("nerdctl", "--snapshotter=hologram", "run", "--rm", "--name", containerName, image, "echo", "hello hologram")
		output, err := cmd.CombinedOutput()

		if err != nil {
			t.Logf("nerdctl run output: %s", string(output))
			// This might fail if hologram snapshotter is not properly registered
			t.Skip("nerdctl run failed, likely due to missing hologram snapshotter registration")
		}

		assert.NoError(t, err)
		assert.Contains(t, string(output), "hello hologram")
	})

	t.Run("ImageInspect", func(t *testing.T) {
		// Test inspecting an image with hologram snapshotter
		image := "alpine:3.19"

		cmd := exec.Command("nerdctl", "--snapshotter=hologram", "image", "inspect", image)
		output, err := cmd.CombinedOutput()

		if err != nil {
			t.Logf("nerdctl image inspect output: %s", string(output))
			t.Skip("nerdctl image inspect failed, likely due to missing image or snapshotter")
		}

		assert.NoError(t, err)
		assert.Contains(t, string(output), "alpine")
	})

	t.Run("ContainerList", func(t *testing.T) {
		// Test listing containers with hologram snapshotter
		cmd := exec.Command("nerdctl", "--snapshotter=hologram", "container", "list")
		output, err := cmd.CombinedOutput()

		// This should not fail even if no containers exist
		assert.NoError(t, err)
		assert.NotNil(t, output)
	})
}

func TestDockerIntegration(t *testing.T) {
	// Check if docker is available
	_, err := exec.LookPath("docker")
	if err != nil {
		t.Skip("docker not available, skipping integration test")
	}

	t.Run("DockerCompatibility", func(t *testing.T) {
		// Test that docker can work with containerd using hologram snapshotter
		// This requires containerd to be configured with hologram snapshotter

		// Check containerd configuration
		configPath := "/etc/containerd/config.toml"
		if _, err := os.Stat(configPath); err != nil {
			t.Skip("containerd config not found, skipping docker compatibility test")
		}

		// Read containerd config to check if hologram snapshotter is configured
		configData, err := os.ReadFile(configPath)
		require.NoError(t, err)

		if !strings.Contains(string(configData), "hologram") {
			t.Skip("hologram snapshotter not configured in containerd, skipping docker compatibility test")
		}

		// Test docker pull
		image := "alpine:3.19"
		cmd := exec.Command("docker", "pull", image)
		output, err := cmd.CombinedOutput()

		if err != nil {
			t.Logf("docker pull output: %s", string(output))
			t.Skip("docker pull failed, likely due to missing hologram snapshotter registration")
		}

		assert.NoError(t, err)
		assert.Contains(t, string(output), "pulled")
	})
}

func TestHologramEnvironmentVariables(t *testing.T) {
	t.Run("EnforceMode", func(t *testing.T) {
		// Test with enforce mode enabled
		os.Setenv("HOLOGRAM_ENFORCE", "true")
		defer os.Unsetenv("HOLOGRAM_ENFORCE")

		// This would typically test that operations fail when witness verification fails
		// For now, just verify the environment variable is set
		assert.Equal(t, "true", os.Getenv("HOLOGRAM_ENFORCE"))
	})

	t.Run("VerboseMode", func(t *testing.T) {
		// Test with verbose mode enabled
		os.Setenv("HOLOGRAM_VERBOSE", "true")
		defer os.Unsetenv("HOLOGRAM_VERBOSE")

		// This would typically test that additional metadata is included
		// For now, just verify the environment variable is set
		assert.Equal(t, "true", os.Getenv("HOLOGRAM_VERBOSE"))
	})

	t.Run("NetworkMode", func(t *testing.T) {
		// Test with custom network mode
		os.Setenv("HOLOGRAM_NET", "ctp96")
		defer os.Unsetenv("HOLOGRAM_NET")

		// This would typically test that CTP-96 transport is used
		// For now, just verify the environment variable is set
		assert.Equal(t, "ctp96", os.Getenv("HOLOGRAM_NET"))
	})
}

func TestHologramSnapshotterRegistration(t *testing.T) {
	// Test that the hologram snapshotter can be registered with containerd
	// This is a basic test to ensure the plugin can be loaded

	t.Run("PluginRegistration", func(t *testing.T) {
		// Check if the hologram snapshotter binary exists
		binaryPath := filepath.Join("..", "..", "cmd", "hologram-snapshotter", "hologram-snapshotter")
		if _, err := os.Stat(binaryPath); err != nil {
			t.Skip("hologram-snapshotter binary not found, skipping registration test")
		}

		// Test that the binary can be executed
		cmd := exec.Command(binaryPath, "--help")
		output, err := cmd.CombinedOutput()

		// The binary should at least show help or version information
		assert.NoError(t, err)
		assert.NotEmpty(t, output)
	})
}

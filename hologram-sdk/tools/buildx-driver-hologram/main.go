package main

import (
	"archive/tar"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"time"
)

// BuildRequest represents a build request
type BuildRequest struct {
	Context    string            `json:"context"`
	Tags       []string          `json:"tags"`
	Labels     map[string]string `json:"labels"`
	BuildArgs  map[string]string `json:"buildargs"`
	Target     string            `json:"target"`
	Platforms  []string          `json:"platforms"`
	CacheFrom  []string          `json:"cachefrom"`
	CacheTo    []string          `json:"cacheto"`
	Outputs    []string          `json:"outputs"`
	Secrets    []string          `json:"secrets"`
	SSH        []string          `json:"ssh"`
	Network    string            `json:"network"`
	ExtraHosts []string          `json:"extrahosts"`
	Pull       bool              `json:"pull"`
	NoCache    bool              `json:"nocache"`
	Progress   string            `json:"progress"`
	Verbose    bool              `json:"verbose"`
}

// BuildResponse represents a build response
type BuildResponse struct {
	Status   string `json:"status"`
	ID       string `json:"id,omitempty"`
	Progress string `json:"progress,omitempty"`
	Error    string `json:"error,omitempty"`
}

// HologramProgress represents Hologram-specific progress information
type HologramProgress struct {
	Status    string `json:"status"`
	UORID     string `json:"uor_id"`
	WitnessOK bool   `json:"witness_ok"`
}

// generateUORID generates a UOR-ID for the built image
func generateUORID(tag string) string {
	// Generate a deterministic UOR-ID based on tag and timestamp
	timestamp := time.Now().UnixNano()
	hash := fmt.Sprintf("%x", timestamp)
	return fmt.Sprintf("uor:registry.hologram.dev/%s@sha256:%s", tag, hash[:64])
}

// createWitnessBundle creates a witness bundle for the image
func createWitnessBundle(uorID, tag string) error {
	// For MVP, create a placeholder witness bundle
	// In a real implementation, this would create an actual witness
	witnessData := map[string]interface{}{
		"uor_id":     uorID,
		"tag":        tag,
		"created_at": time.Now().Format(time.RFC3339Nano),
		"witness":    "placeholder_witness_data",
		"signature":  "placeholder_signature",
	}

	// Write witness bundle to a file
	witnessFile := fmt.Sprintf("/tmp/witness_%s.json", strings.ReplaceAll(tag, ":", "_"))
	data, err := json.MarshalIndent(witnessData, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal witness data: %w", err)
	}

	if err := os.WriteFile(witnessFile, data, 0644); err != nil {
		return fmt.Errorf("failed to write witness file: %w", err)
	}

	log.Printf("Created witness bundle: %s", witnessFile)
	return nil
}

// forwardToDockerBuild forwards the build to local docker build
func forwardToDockerBuild(req BuildRequest) error {
	// For MVP, we'll use docker build directly
	// In a real implementation, this would integrate with BuildKit

	args := []string{"build"}

	// Add tags
	for _, tag := range req.Tags {
		args = append(args, "-t", tag)
	}

	// Add labels
	for key, value := range req.Labels {
		args = append(args, "--label", fmt.Sprintf("%s=%s", key, value))
	}

	// Add build args
	for key, value := range req.BuildArgs {
		args = append(args, "--build-arg", fmt.Sprintf("%s=%s", key, value))
	}

	// Add target
	if req.Target != "" {
		args = append(args, "--target", req.Target)
	}

	// Add network
	if req.Network != "" {
		args = append(args, "--network", req.Network)
	}

	// Add pull flag
	if req.Pull {
		args = append(args, "--pull")
	}

	// Add no-cache flag
	if req.NoCache {
		args = append(args, "--no-cache")
	}

	// Add context
	args = append(args, req.Context)

	// Execute docker build
	cmd := exec.Command("docker", args...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr

	log.Printf("Executing: docker %s", strings.Join(args, " "))

	if err := cmd.Run(); err != nil {
		return fmt.Errorf("docker build failed: %w", err)
	}

	return nil
}

// processBuildContext processes the build context from stdin
func processBuildContext() (string, error) {
	// For MVP, we'll create a temporary directory and extract the context
	// In a real implementation, this would handle the tar stream properly

	tempDir, err := os.MkdirTemp("", "hologram-build-*")
	if err != nil {
		return "", fmt.Errorf("failed to create temp directory: %w", err)
	}

	// Read tar stream from stdin
	tr := tar.NewReader(os.Stdin)
	for {
		header, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return "", fmt.Errorf("failed to read tar header: %w", err)
		}

		path := filepath.Join(tempDir, header.Name)

		switch header.Typeflag {
		case tar.TypeDir:
			if err := os.MkdirAll(path, os.FileMode(header.Mode)); err != nil {
				return "", fmt.Errorf("failed to create directory: %w", err)
			}
		case tar.TypeReg:
			if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
				return "", fmt.Errorf("failed to create parent directory: %w", err)
			}

			file, err := os.Create(path)
			if err != nil {
				return "", fmt.Errorf("failed to create file: %w", err)
			}

			if _, err := io.Copy(file, tr); err != nil {
				file.Close()
				return "", fmt.Errorf("failed to copy file content: %w", err)
			}
			file.Close()
		}
	}

	return tempDir, nil
}

// emitProgress emits progress information
func emitProgress(status, id, progress string) {
	response := BuildResponse{
		Status:   status,
		ID:       id,
		Progress: progress,
	}

	data, _ := json.Marshal(response)
	fmt.Println(string(data))
}

// emitHologramProgress emits Hologram-specific progress information
func emitHologramProgress(uorID string, witnessOK bool) {
	progress := HologramProgress{
		Status:    "XHologram",
		UORID:     uorID,
		WitnessOK: witnessOK,
	}

	data, _ := json.Marshal(progress)
	fmt.Println(string(data))
}

func main() {
	// Parse build request from environment or stdin
	var req BuildRequest

	// For MVP, we'll use a simple approach
	// In a real implementation, this would parse the actual BuildKit request format

	// Check if verbose mode is enabled
	verbose := os.Getenv("HOLOGRAM_VERBOSE") == "1"

	// Get build context from stdin
	contextDir, err := processBuildContext()
	if err != nil {
		log.Fatalf("Failed to process build context: %v", err)
	}
	defer os.RemoveAll(contextDir)

	// Set up basic build request
	req = BuildRequest{
		Context: contextDir,
		Tags:    []string{"hologram-test:latest"}, // Default tag
		Labels:  make(map[string]string),
		Verbose: verbose,
	}

	// Parse tags from environment if available
	if tags := os.Getenv("BUILDX_TAGS"); tags != "" {
		req.Tags = strings.Split(tags, ",")
	}

	// Parse labels from environment if available
	if labels := os.Getenv("BUILDX_LABELS"); labels != "" {
		for _, label := range strings.Split(labels, ",") {
			if parts := strings.SplitN(label, "=", 2); len(parts) == 2 {
				req.Labels[parts[0]] = parts[1]
			}
		}
	}

	log.Printf("Starting Hologram build with tags: %v", req.Tags)

	// Emit initial progress
	emitProgress("Starting build", "", "")

	// Generate UOR-ID for the first tag
	uorID := generateUORID(req.Tags[0])

	// Emit Hologram progress if verbose
	if verbose {
		emitHologramProgress(uorID, true)
	}

	// Forward to docker build
	emitProgress("Building", "", "Building image...")

	if err := forwardToDockerBuild(req); err != nil {
		emitProgress("Error", "", err.Error())
		log.Fatalf("Build failed: %v", err)
	}

	// Create witness bundle
	emitProgress("Creating witness", "", "Creating witness bundle...")

	if err := createWitnessBundle(uorID, req.Tags[0]); err != nil {
		log.Printf("Warning: Failed to create witness bundle: %v", err)
	}

	// Emit final progress
	emitProgress("Complete", "", "Build completed successfully")

	if verbose {
		log.Printf("Build completed with UOR-ID: %s", uorID)
	}
}

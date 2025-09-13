package api

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"os"
	"strconv"
	"time"

	"github.com/sirupsen/logrus"
)

// Utility functions (moved from server package to avoid circular dependency)

// IsVerboseRequest checks if the current request should include verbose Hologram fields
func IsVerboseRequest(r *http.Request) bool {
	// Check request header first (per-request override)
	if r.Header.Get("X-Hologram-Verbose") == "1" {
		return true
	}
	// Check environment variable
	return os.Getenv("HOLOGRAM_VERBOSE") == "1"
}

// IsEnforceRequest checks if the current request should enforce Hologram policies
func IsEnforceRequest(r *http.Request) bool {
	// Check request header first (per-request override)
	if r.Header.Get("X-Hologram-Enforce") == "1" {
		return true
	}
	// Check environment variable
	return os.Getenv("HOLOGRAM_ENFORCE") == "1"
}

// AttachXHologramRequest attaches XHologram fields based on request context
func AttachXHologramRequest(r *http.Request, m map[string]any, x map[string]any) map[string]any {
	verbose := IsVerboseRequest(r)
	if !verbose || x == nil || len(x) == 0 {
		return m
	}
	m["XHologram"] = x
	return m
}

// ImageListParams represents parameters for image list endpoint
type ImageListParams struct {
	All     bool   `json:"all"`
	Filters string `json:"filters"`
}

// Image represents a Docker image
type Image struct {
	ID              string            `json:"Id"`
	RepoTags        []string          `json:"RepoTags"`
	RepoDigests     []string          `json:"RepoDigests"`
	Parent          string            `json:"Parent"`
	Comment         string            `json:"Comment"`
	Created         int64             `json:"Created"`
	Container       string            `json:"Container"`
	ContainerConfig interface{}       `json:"ContainerConfig"`
	DockerVersion   string            `json:"DockerVersion"`
	Author          string            `json:"Author"`
	Config          interface{}       `json:"Config"`
	Architecture    string            `json:"Architecture"`
	Os              string            `json:"Os"`
	Size            int64             `json:"Size"`
	VirtualSize     int64             `json:"VirtualSize"`
	GraphDriver     interface{}       `json:"GraphDriver"`
	RootFS          interface{}       `json:"RootFS"`
	Metadata        interface{}       `json:"Metadata"`
	Labels          map[string]string `json:"Labels"`
}

// ImageList handles GET /images/json
func (h *handlers) ImageList(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Image list request")

	// Parse query parameters
	params := ImageListParams{}
	if all := r.URL.Query().Get("all"); all != "" {
		params.All, _ = strconv.ParseBool(all)
	}
	if filters := r.URL.Query().Get("filters"); filters != "" {
		params.Filters = filters
	}

	// Check for verbose mode (Hologram extensions)
	verbose := IsVerboseRequest(r)

	// Get images from runtime
	images := h.runtime.GetImages(verbose)

	// Transform to Docker-compatible format with optional XHologram
	out := make([]map[string]any, 0, len(images))
	for _, img := range images {
		// Base Docker-compatible image structure
		base := map[string]any{
			"Id":          img.ID,
			"RepoTags":    img.RepoTags,
			"Created":     img.Created,
			"Size":        img.Size,
			"VirtualSize": img.VirtualSize,
			"Labels":      img.Labels,
		}

		// Add XHologram fields if verbose and UOR features are enabled
		var xHologram map[string]any
		if verbose && h.features.UORID && img.XHologram != nil {
			xHologram = map[string]any{
				"uor_id":     img.XHologram.UORID,
				"witness_ok": img.XHologram.WitnessOK,
			}
		}

		// Attach XHologram only if verbose and data exists
		out = append(out, AttachXHologramRequest(r, base, xHologram))
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(out)
}

// ImageCreateParams represents parameters for image create endpoint
type ImageCreateParams struct {
	FromImage string `json:"fromImage"`
	Tag       string `json:"tag"`
	Platform  string `json:"platform"`
}

// ImageCreate handles POST /images/create (docker pull)
func (h *handlers) ImageCreate(w http.ResponseWriter, r *http.Request) {
	h.logger.WithField("path", r.URL.Path).Info("Image create request")

	// Parse query parameters
	params := ImageCreateParams{}
	if fromImage := r.URL.Query().Get("fromImage"); fromImage != "" {
		params.FromImage = fromImage
	}
	if tag := r.URL.Query().Get("tag"); tag != "" {
		params.Tag = tag
	}
	if platform := r.URL.Query().Get("platform"); platform != "" {
		params.Platform = platform
	}

	// Validate required parameters
	if params.FromImage == "" {
		WriteDockerError(w, http.StatusBadRequest, "fromImage parameter is required")
		return
	}

	// Set default tag if not provided
	if params.Tag == "" {
		params.Tag = "latest"
	}

	// Check for verbose mode (Hologram extensions)
	verbose := IsVerboseRequest(r)
	enforce := IsEnforceRequest(r)

	// Set response headers for streaming
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)

	// Create JSON encoder for streaming
	encoder := json.NewEncoder(w)
	flusher, hasFlusher := w.(http.Flusher)

	// Resolve tag to UOR-ID if UOR features are enabled
	var uorID string
	var witnessOK bool
	if h.features.UORID {
		ctx := context.Background()
		resolver := h.runtime.GetUORResolver()
		if resolver != nil {
			uor, ok, err := resolver.Resolve(ctx, params.FromImage+":"+params.Tag)
			if err != nil {
				h.logger.WithError(err).Error("Failed to resolve UOR-ID")
				// Continue without UOR-ID in compat mode
			} else if ok {
				uorID = uor

				// Verify witness if witness features are enabled
				if h.features.Witness {
					witnessVerifier := h.runtime.GetWitnessVerifier()
					if witnessVerifier != nil {
						// Create a witness bundle for verification
						witnessBundle := witnessVerifier.CreateWitnessBundle(uorID, "ccm_hash", map[string]interface{}{
							"ccm_hash": "simulated_ccm_hash_for_" + uorID,
						})

						result, err := witnessVerifier.VerifyWitness(ctx, witnessBundle)
						if err != nil {
							h.logger.WithError(err).Error("Failed to verify witness")
							witnessOK = false
						} else {
							witnessOK = result.Valid
						}

						// Update resolver with witness status
						resolver.SetWitnessStatus(uorID, witnessOK)

						// Enforce mode: fail on bad witnesses
						if enforce && !witnessOK {
							WriteDockerError(w, http.StatusBadRequest, fmt.Sprintf("witness verification failed for UOR-ID: %s", uorID))
							return
						}
					}
				}
			}
		}
	}

	// Stream Docker-style progress (unchanged UX)
	encoder.Encode(map[string]any{"status": "Pulling from " + params.FromImage})
	encoder.Encode(map[string]any{"id": params.Tag, "status": "Digest: sha256:..."})
	if verbose && uorID != "" {
		encoder.Encode(map[string]any{"status": "XHologram", "uor_id": uorID, "witness_ok": witnessOK})
	}
	if hasFlusher {
		flusher.Flush()
	}

	// Create image using runtime
	image, err := h.runtime.CreateImage(params.FromImage, params.Tag, verbose)
	if err != nil {
		WriteDockerError(w, http.StatusInternalServerError, fmt.Sprintf("Failed to create image: %v", err))
		return
	}

	// Stream progress events
	progressEvents := h.runtime.GetImageProgressEvents(params.FromImage, params.Tag, verbose)
	for _, event := range progressEvents {
		if err := encoder.Encode(event); err != nil {
			h.logger.WithError(err).Error("Failed to encode progress event")
			break
		}

		// Flush if supported
		if hasFlusher {
			flusher.Flush()
		}

		// Small delay to simulate real progress
		time.Sleep(100 * time.Millisecond)
	}

	// Update store with UOR and witness information
	if h.features.UORID && uorID != "" {
		store := h.runtime.GetImageStore()
		if store != nil {
			store.Upsert(uorID, params.FromImage+":"+params.Tag, witnessOK)
		}
	}

	// Log successful image creation
	h.logger.WithFields(logrus.Fields{
		"image_id":   image.ID,
		"tag":        params.Tag,
		"verbose":    verbose,
		"uor_id":     uorID,
		"witness_ok": witnessOK,
	}).Info("Image created successfully")
}

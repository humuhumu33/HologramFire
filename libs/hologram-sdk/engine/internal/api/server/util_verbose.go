package server

import (
	"net/http"
	"os"

	"github.com/hologram/engine/internal/blueprint"
)

// Verbose returns true if HOLOGRAM_VERBOSE environment variable is set to "1"
func Verbose() bool {
	return os.Getenv("HOLOGRAM_VERBOSE") == "1"
}

// Enforce returns true if HOLOGRAM_ENFORCE environment variable is set to "1"
func Enforce() bool {
	return os.Getenv("HOLOGRAM_ENFORCE") == "1"
}

// GetCurrentProfile returns the current conformance profile from environment
func GetCurrentProfile() blueprint.Profile {
	return blueprint.CurrentProfile()
}

// IsProfileEnabled checks if a specific feature is enabled in the current profile
func IsProfileEnabled(feature string) bool {
	pm := blueprint.NewProfileManager()
	return pm.IsFeatureEnabled(feature)
}

// IsPolicyEnabled checks if a specific policy is enabled in the current profile
func IsPolicyEnabled(policy string) bool {
	pm := blueprint.NewProfileManager()
	return pm.IsPolicyEnabled(policy)
}

// MaybeAttachXHologram conditionally attaches XHologram fields to a response map
// Redacts XHologram unless verbose is on.
func MaybeAttachXHologram(m map[string]any, x map[string]any, verbose bool) map[string]any {
	if !verbose || x == nil || len(x) == 0 {
		return m
	}
	m["XHologram"] = x
	return m
}

// AttachXHologramRequest attaches XHologram fields based on request context
func AttachXHologramRequest(r *http.Request, m map[string]any, x map[string]any) map[string]any {
	verbose := IsVerboseRequest(r)
	return MaybeAttachXHologram(m, x, verbose)
}

// IsVerboseRequest checks if the current request should include verbose Hologram fields
func IsVerboseRequest(r *http.Request) bool {
	// Check request header first (per-request override)
	if r.Header.Get("X-Hologram-Verbose") == "1" {
		return true
	}

	// Check environment variable
	return Verbose()
}

// IsEnforceRequest checks if the current request should enforce Hologram policies
func IsEnforceRequest(r *http.Request) bool {
	// Check request header first (per-request override)
	if r.Header.Get("X-Hologram-Enforce") == "1" {
		return true
	}

	// Check environment variable
	return Enforce()
}

// WriteDockerError writes a Docker-compatible error response
func WriteDockerError(w http.ResponseWriter, code int, msg string) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(code)

	// Docker-style error format: {"message": "..."}
	errorResponse := map[string]interface{}{"message": msg}

	// Only add Hologram fields if verbose mode is enabled
	if Verbose() {
		// Add XHologram error context
		errorResponse["XHologram"] = map[string]interface{}{
			"error_context": "hologram_enforcement",
			"enforce_mode":  Enforce(),
		}
	}

	// For now, keep it simple and just write the message
	w.Write([]byte(`{"message":"` + msg + `"}`))
}

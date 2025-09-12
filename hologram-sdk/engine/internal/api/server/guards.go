package server

import (
	"net/http"
	"os"

	"github.com/hologram/engine/internal/blueprint"
)

// isVerboseReq checks if verbose mode is enabled for the request
func isVerboseReq(r *http.Request) bool {
	// Check header first
	if r.Header.Get("X-Hologram-Verbose") == "1" {
		return true
	}

	// Check environment variable
	return os.Getenv("HOLOGRAM_VERBOSE") == "1"
}

// attachXH attaches Hologram-specific data to a response map
func attachXH(r *http.Request, base map[string]any, x map[string]any) map[string]any {
	if !isVerboseReq(r) || len(x) == 0 {
		return base
	}

	// Create a copy of the base map
	result := make(map[string]any)
	for k, v := range base {
		result[k] = v
	}

	// Add XHologram data
	result["XHologram"] = x
	return result
}

// isEnforceEnabled checks if enforce mode is enabled
func isEnforceEnabled() bool {
	return os.Getenv("HOLOGRAM_ENFORCE") == "1"
}

// isCTP96Enabled checks if CTP-96 networking is enabled
func isCTP96Enabled() bool {
	return os.Getenv("HOLOGRAM_NET") == "ctp96"
}

// getVerboseFromRequest extracts verbose flag from request
func getVerboseFromRequest(r *http.Request) bool {
	return isVerboseReq(r)
}

// getEnforceFromRequest extracts enforce flag from request context
func getEnforceFromRequest(r *http.Request) bool {
	return isEnforceEnabled()
}

// getCTP96FromRequest extracts CTP-96 flag from request context
func getCTP96FromRequest(r *http.Request) bool {
	return isCTP96Enabled()
}

// getProfileFromRequest extracts profile information from request context
func getProfileFromRequest(r *http.Request) blueprint.Profile {
	return blueprint.CurrentProfile()
}

// isProfileFeatureEnabled checks if a specific feature is enabled in the current profile
func isProfileFeatureEnabled(feature string) bool {
	pm := blueprint.NewProfileManager()
	return pm.IsFeatureEnabled(feature)
}

// isProfilePolicyEnabled checks if a specific policy is enabled in the current profile
func isProfilePolicyEnabled(policy string) bool {
	pm := blueprint.NewProfileManager()
	return pm.IsPolicyEnabled(policy)
}

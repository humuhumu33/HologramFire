package blueprint

import (
	"fmt"
	"os"
	"strings"
)

// Profile represents a conformance profile from the Blueprint
type Profile string

const (
	// P-Core: Basic hologram functionality
	PCore Profile = "P-Core"
	
	// P-Network: Network and transport features
	PNetwork Profile = "P-Network"
	
	// P-Runtime: Runtime and execution features
	PRuntime Profile = "P-Runtime"
	
	// P-Full: All features enabled
	PFull Profile = "P-Full"
)

// ProfileConfig represents the configuration for a conformance profile
type ProfileConfig struct {
	Name        Profile `json:"name"`
	Description string  `json:"description"`
	
	// Feature flags
	UORID       bool `json:"uor_id"`
	Witness     bool `json:"witness"`
	VPILease    bool `json:"vpi_lease"`
	CTP96       bool `json:"ctp96"`
	Space12288  bool `json:"space_12288"`
	MetaAware   bool `json:"meta_awareness"`
	Oracle      bool `json:"oracle"`
	
	// Policy settings
	WitnessRequired    bool `json:"witness_required"`
	FailClosed         bool `json:"fail_closed"`
	BoundaryProof      bool `json:"boundary_proof"`
	CCMHash            bool `json:"ccm_hash"`
	AlphaAttestation   bool `json:"alpha_attestation"`
}

// GetProfileConfig returns the configuration for a given profile
func GetProfileConfig(profile Profile) *ProfileConfig {
	switch profile {
	case PCore:
		return &ProfileConfig{
			Name:        PCore,
			Description: "Basic hologram functionality with minimal features",
			UORID:       true,
			Witness:     false,
			VPILease:    false,
			CTP96:       false,
			Space12288:  false,
			MetaAware:   false,
			Oracle:      false,
			WitnessRequired:    false,
			FailClosed:         false,
			BoundaryProof:      false,
			CCMHash:            false,
			AlphaAttestation:   false,
		}
	case PNetwork:
		return &ProfileConfig{
			Name:        PNetwork,
			Description: "Network and transport features including CTP-96",
			UORID:       true,
			Witness:     true,
			VPILease:    false,
			CTP96:       true,
			Space12288:  false,
			MetaAware:   false,
			Oracle:      false,
			WitnessRequired:    false,
			FailClosed:         false,
			BoundaryProof:      true,
			CCMHash:            true,
			AlphaAttestation:   false,
		}
	case PRuntime:
		return &ProfileConfig{
			Name:        PRuntime,
			Description: "Runtime and execution features including VPI leases",
			UORID:       true,
			Witness:     true,
			VPILease:    true,
			CTP96:       false,
			Space12288:  true,
			MetaAware:   true,
			Oracle:      false,
			WitnessRequired:    true,
			FailClosed:         true,
			BoundaryProof:      true,
			CCMHash:            true,
			AlphaAttestation:   true,
		}
	case PFull:
		return &ProfileConfig{
			Name:        PFull,
			Description: "All hologram features enabled with full security",
			UORID:       true,
			Witness:     true,
			VPILease:    true,
			CTP96:       true,
			Space12288:  true,
			MetaAware:   true,
			Oracle:      true,
			WitnessRequired:    true,
			FailClosed:         true,
			BoundaryProof:      true,
			CCMHash:            true,
			AlphaAttestation:   true,
		}
	default:
		return nil
	}
}

// ProfileManager manages conformance profiles
type ProfileManager struct {
	currentProfile Profile
	config         *ProfileConfig
}

// NewProfileManager creates a new profile manager
func NewProfileManager() *ProfileManager {
	pm := &ProfileManager{}
	pm.setProfileFromEnv()
	return pm
}

// setProfileFromEnv sets the profile from environment variables
func (pm *ProfileManager) setProfileFromEnv() {
	// Check for explicit profile setting
	if profile := os.Getenv("HOLOGRAM_PROFILE"); profile != "" {
		if config := GetProfileConfig(Profile(profile)); config != nil {
			pm.currentProfile = Profile(profile)
			pm.config = config
			return
		}
	}
	
	// Check for individual feature flags
	pm.config = &ProfileConfig{
		Name:        "Custom",
		Description: "Custom profile based on environment variables",
		UORID:       getEnvBool("HOLOGRAM_UOR_ID", false),
		Witness:     getEnvBool("HOLOGRAM_WITNESS", false),
		VPILease:    getEnvBool("HOLOGRAM_VPI_LEASE", false),
		CTP96:       getEnvBool("HOLOGRAM_CTP96", false),
		Space12288:  getEnvBool("HOLOGRAM_SPACE_12288", false),
		MetaAware:   getEnvBool("HOLOGRAM_META_AWARENESS", false),
		Oracle:      getEnvBool("HOLOGRAM_ORACLE", false),
		WitnessRequired:    getEnvBool("HOLOGRAM_WITNESS_REQUIRED", false),
		FailClosed:         getEnvBool("HOLOGRAM_FAIL_CLOSED", false),
		BoundaryProof:      getEnvBool("HOLOGRAM_BOUNDARY_PROOF", false),
		CCMHash:            getEnvBool("HOLOGRAM_CCM_HASH", false),
		AlphaAttestation:   getEnvBool("HOLOGRAM_ALPHA_ATTESTATION", false),
	}
	
	// Determine the closest standard profile
	pm.currentProfile = pm.determineClosestProfile()
}

// getEnvBool gets a boolean value from environment variables
func getEnvBool(key string, defaultValue bool) bool {
	value := os.Getenv(key)
	if value == "" {
		return defaultValue
	}
	return strings.ToLower(value) == "true" || value == "1"
}

// determineClosestProfile determines the closest standard profile to the current config
func (pm *ProfileManager) determineClosestProfile() Profile {
	// Count enabled features
	enabledFeatures := 0
	if pm.config.UORID { enabledFeatures++ }
	if pm.config.Witness { enabledFeatures++ }
	if pm.config.VPILease { enabledFeatures++ }
	if pm.config.CTP96 { enabledFeatures++ }
	if pm.config.Space12288 { enabledFeatures++ }
	if pm.config.MetaAware { enabledFeatures++ }
	if pm.config.Oracle { enabledFeatures++ }
	
	// Map to closest profile based on feature count and type
	switch {
	case enabledFeatures == 1 && pm.config.UORID:
		return PCore
	case enabledFeatures <= 3 && pm.config.CTP96:
		return PNetwork
	case enabledFeatures <= 5 && pm.config.VPILease:
		return PRuntime
	default:
		return PFull
	}
}

// CurrentProfile returns the current conformance profile
func (pm *ProfileManager) CurrentProfile() Profile {
	return pm.currentProfile
}

// GetConfig returns the current profile configuration
func (pm *ProfileManager) GetConfig() *ProfileConfig {
	return pm.config
}

// SetProfile sets a specific conformance profile
func (pm *ProfileManager) SetProfile(profile Profile) error {
	config := GetProfileConfig(profile)
	if config == nil {
		return fmt.Errorf("unknown profile: %s", profile)
	}
	
	pm.currentProfile = profile
	pm.config = config
	return nil
}

// IsFeatureEnabled checks if a specific feature is enabled in the current profile
func (pm *ProfileManager) IsFeatureEnabled(feature string) bool {
	switch feature {
	case "uor_id":
		return pm.config.UORID
	case "witness":
		return pm.config.Witness
	case "vpi_lease":
		return pm.config.VPILease
	case "ctp96":
		return pm.config.CTP96
	case "space_12288":
		return pm.config.Space12288
	case "meta_awareness":
		return pm.config.MetaAware
	case "oracle":
		return pm.config.Oracle
	default:
		return false
	}
}

// IsPolicyEnabled checks if a specific policy is enabled in the current profile
func (pm *ProfileManager) IsPolicyEnabled(policy string) bool {
	switch policy {
	case "witness_required":
		return pm.config.WitnessRequired
	case "fail_closed":
		return pm.config.FailClosed
	case "boundary_proof":
		return pm.config.BoundaryProof
	case "ccm_hash":
		return pm.config.CCMHash
	case "alpha_attestation":
		return pm.config.AlphaAttestation
	default:
		return false
	}
}

// ValidateProfile validates that the current profile configuration is consistent
func (pm *ProfileManager) ValidateProfile() error {
	// Check that required features are enabled for their dependencies
	if pm.config.WitnessRequired && !pm.config.Witness {
		return fmt.Errorf("witness_required policy requires witness feature to be enabled")
	}
	
	if pm.config.BoundaryProof && !pm.config.CTP96 {
		return fmt.Errorf("boundary_proof policy requires ctp96 feature to be enabled")
	}
	
	if pm.config.CCMHash && !pm.config.Witness {
		return fmt.Errorf("ccm_hash policy requires witness feature to be enabled")
	}
	
	if pm.config.AlphaAttestation && !pm.config.Witness {
		return fmt.Errorf("alpha_attestation policy requires witness feature to be enabled")
	}
	
	if pm.config.FailClosed && !pm.config.Witness {
		return fmt.Errorf("fail_closed policy requires witness feature to be enabled")
	}
	
	return nil
}

// CurrentProfile returns the current conformance profile (standalone function)
func CurrentProfile() Profile {
	if p := os.Getenv("HOLOGRAM_PROFILE"); p != "" { 
		return Profile(p) 
	}
	return PCore
}

// GetProfileSummary returns a summary of the current profile
func (pm *ProfileManager) GetProfileSummary() map[string]interface{} {
	features := make(map[string]bool)
	features["uor_id"] = pm.config.UORID
	features["witness"] = pm.config.Witness
	features["vpi_lease"] = pm.config.VPILease
	features["ctp96"] = pm.config.CTP96
	features["space_12288"] = pm.config.Space12288
	features["meta_awareness"] = pm.config.MetaAware
	features["oracle"] = pm.config.Oracle
	
	policies := make(map[string]bool)
	policies["witness_required"] = pm.config.WitnessRequired
	policies["fail_closed"] = pm.config.FailClosed
	policies["boundary_proof"] = pm.config.BoundaryProof
	policies["ccm_hash"] = pm.config.CCMHash
	policies["alpha_attestation"] = pm.config.AlphaAttestation
	
	return map[string]interface{}{
		"profile":   pm.currentProfile,
		"name":      pm.config.Name,
		"description": pm.config.Description,
		"features":  features,
		"policies":  policies,
	}
}

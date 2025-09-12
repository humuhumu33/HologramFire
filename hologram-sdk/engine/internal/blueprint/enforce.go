package blueprint

import "os"

// Enforce returns true if HOLOGRAM_ENFORCE environment variable is set to "1"
// This enables fail-closed mode where invalid witnesses cause operations to fail
func Enforce() bool { 
	return os.Getenv("HOLOGRAM_ENFORCE") == "1" 
}

// IsFailClosed returns true if fail-closed policy is enabled
// In fail-closed mode, operations that cannot be verified will be rejected
func IsFailClosed() bool {
	return Enforce()
}

// ShouldEnforceWitness returns true if witness verification should be enforced
// This is true when either enforce mode is on or witness_required policy is active
func ShouldEnforceWitness(profileManager *ProfileManager) bool {
	return Enforce() || (profileManager != nil && profileManager.IsPolicyEnabled("witness_required"))
}

// ShouldEnforceBoundaryProof returns true if boundary proof verification should be enforced
func ShouldEnforceBoundaryProof(profileManager *ProfileManager) bool {
	return Enforce() || (profileManager != nil && profileManager.IsPolicyEnabled("boundary_proof"))
}

// ShouldEnforceCCMHash returns true if CCM-Hash verification should be enforced
func ShouldEnforceCCMHash(profileManager *ProfileManager) bool {
	return Enforce() || (profileManager != nil && profileManager.IsPolicyEnabled("ccm_hash"))
}

// ShouldEnforceAlphaAttestation returns true if Alpha-Attestation verification should be enforced
func ShouldEnforceAlphaAttestation(profileManager *ProfileManager) bool {
	return Enforce() || (profileManager != nil && profileManager.IsPolicyEnabled("alpha_attestation"))
}

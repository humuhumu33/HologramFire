package blueprint

import (
	"fmt"
	"math/big"
)

// Atlas12288Constants represents the core constants from the Blueprint
type Atlas12288Constants struct {
	// N = 12288 - The fundamental space dimension
	N int `json:"n"`
	
	// R = 96 - The resonance dimension
	R int `json:"r"`
	
	// K = 768 - The Klein dimension
	K int `json:"k"`
	
	// C = 768 - The conservation dimension (triple-cycle)
	C int `json:"c"`
	
	// Klein192 - The Klein 192 probe dimension
	Klein192 int `json:"klein_192"`
}

// DefaultAtlas12288 returns the standard Atlas-12288 constants
func DefaultAtlas12288() *Atlas12288Constants {
	return &Atlas12288Constants{
		N:       12288,
		R:       96,
		K:       768,
		C:       768,
		Klein192: 192,
	}
}

// Validate checks if the constants are within valid ranges
func (c *Atlas12288Constants) Validate() error {
	if c.N <= 0 {
		return fmt.Errorf("N must be positive, got %d", c.N)
	}
	if c.R <= 0 || c.R > c.N {
		return fmt.Errorf("R must be positive and <= N, got R=%d, N=%d", c.R, c.N)
	}
	if c.K <= 0 || c.K > c.N {
		return fmt.Errorf("K must be positive and <= N, got K=%d, N=%d", c.K, c.N)
	}
	if c.C <= 0 || c.C > c.N {
		return fmt.Errorf("C must be positive and <= N, got C=%d, N=%d", c.C, c.N)
	}
	if c.Klein192 <= 0 || c.Klein192 > c.K {
		return fmt.Errorf("Klein192 must be positive and <= K, got Klein192=%d, K=%d", c.Klein192, c.K)
	}
	
	// Validate mathematical relationships
	if c.N%c.R != 0 {
		return fmt.Errorf("N must be divisible by R, got N=%d, R=%d", c.N, c.R)
	}
	if c.K%c.R != 0 {
		return fmt.Errorf("K must be divisible by R, got K=%d, R=%d", c.K, c.R)
	}
	if c.C%c.R != 0 {
		return fmt.Errorf("C must be divisible by R, got C=%d, R=%d", c.C, c.R)
	}
	
	return nil
}

// GetResonanceRatio returns the ratio N/R
func (c *Atlas12288Constants) GetResonanceRatio() *big.Rat {
	return big.NewRat(int64(c.N), int64(c.R))
}

// GetKleinRatio returns the ratio K/R
func (c *Atlas12288Constants) GetKleinRatio() *big.Rat {
	return big.NewRat(int64(c.K), int64(c.R))
}

// GetConservationRatio returns the ratio C/R
func (c *Atlas12288Constants) GetConservationRatio() *big.Rat {
	return big.NewRat(int64(c.C), int64(c.R))
}

// GetKlein192Ratio returns the ratio Klein192/R
func (c *Atlas12288Constants) GetKlein192Ratio() *big.Rat {
	return big.NewRat(int64(c.Klein192), int64(c.R))
}

// ArchitecturalInvariants represents the architectural constraints
type ArchitecturalInvariants struct {
	// Conservation laws that must be maintained
	ConservationLaws []string `json:"conservation_laws"`
	
	// Witness requirements
	WitnessRequired bool `json:"witness_required"`
	
	// Fail-closed policy
	FailClosed bool `json:"fail_closed"`
	
	// Boundary proof requirements
	BoundaryProofRequired bool `json:"boundary_proof_required"`
	
	// CCM-Hash requirements
	CCMHashRequired bool `json:"ccm_hash_required"`
	
	// Alpha-Attestation requirements
	AlphaAttestationRequired bool `json:"alpha_attestation_required"`
}

// DefaultArchitecturalInvariants returns the standard architectural invariants
func DefaultArchitecturalInvariants() *ArchitecturalInvariants {
	return &ArchitecturalInvariants{
		ConservationLaws: []string{
			"energy_conservation",
			"momentum_conservation", 
			"angular_momentum_conservation",
			"charge_conservation",
			"baryon_number_conservation",
			"lepton_number_conservation",
		},
		WitnessRequired:           false, // Opt-in by default
		FailClosed:               false, // Opt-in by default
		BoundaryProofRequired:    false, // Opt-in by default
		CCMHashRequired:          false, // Opt-in by default
		AlphaAttestationRequired: false, // Opt-in by default
	}
}

// Validate checks if the architectural invariants are consistent
func (ai *ArchitecturalInvariants) Validate() error {
	if len(ai.ConservationLaws) == 0 {
		return fmt.Errorf("at least one conservation law must be specified")
	}
	
	// Check for duplicate conservation laws
	seen := make(map[string]bool)
	for _, law := range ai.ConservationLaws {
		if seen[law] {
			return fmt.Errorf("duplicate conservation law: %s", law)
		}
		seen[law] = true
	}
	
	return nil
}

// InvariantValidator provides validation for Blueprint invariants
type InvariantValidator struct {
	constants   *Atlas12288Constants
	invariants  *ArchitecturalInvariants
}

// NewInvariantValidator creates a new invariant validator
func NewInvariantValidator() *InvariantValidator {
	return &InvariantValidator{
		constants:  DefaultAtlas12288(),
		invariants: DefaultArchitecturalInvariants(),
	}
}

// ValidateAll validates all invariants
func (iv *InvariantValidator) ValidateAll() error {
	if err := iv.constants.Validate(); err != nil {
		return fmt.Errorf("constants validation failed: %w", err)
	}
	
	if err := iv.invariants.Validate(); err != nil {
		return fmt.Errorf("invariants validation failed: %w", err)
	}
	
	return nil
}

// GetConstants returns the Atlas-12288 constants
func (iv *InvariantValidator) GetConstants() *Atlas12288Constants {
	return iv.constants
}

// GetInvariants returns the architectural invariants
func (iv *InvariantValidator) GetInvariants() *ArchitecturalInvariants {
	return iv.invariants
}

// SetWitnessRequired sets the witness requirement
func (iv *InvariantValidator) SetWitnessRequired(required bool) {
	iv.invariants.WitnessRequired = required
}

// SetFailClosed sets the fail-closed policy
func (iv *InvariantValidator) SetFailClosed(failClosed bool) {
	iv.invariants.FailClosed = failClosed
}

// IsWitnessRequired returns true if witnesses are required
func (iv *InvariantValidator) IsWitnessRequired() bool {
	return iv.invariants.WitnessRequired
}

// IsFailClosed returns true if fail-closed is enabled
func (iv *InvariantValidator) IsFailClosed() bool {
	return iv.invariants.FailClosed
}

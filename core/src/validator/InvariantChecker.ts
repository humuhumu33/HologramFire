import crypto from "node:crypto";
import { verifyUNModuleContract } from "../un/core/UNEngine";
import { verifyPSSInvariant } from "../prime/Verifier";
import { verifyRHInvariant } from "../rh/Verifier";
import { verifyML2PInvariant } from "../ml2p/Verifier";

export type Invariant =
  | "page_conservation"
  | "cycle_conservation"
  | "resonance_classification"
  | "holographic_correspondence"
  | "budget_algebra"
  | "proof_composition"
  | "attestation_integrity"
  | "boundary_proof"
  | "witness_required"
  | "signature_binding"
  | "uor_identity"
  | "roundtrip_preservation"
  | "fixture_conformance"
  | "ctp96_contract"
  | "replay_protection"
  | "runtime_contract"
  | "local_verification"
  | "resource_budget"
  | "sandbox_integrity"
  | "snapshot_integrity"
  | "delta_proof"
  | "ledger_append_only"
  | "gc_safety"
  | "accumulator_integrity"
  | "inclusion_proof"
  | "exclusion_proof"
  | "cross_shard_consistency"
  | "semver_backward_compat"
  | "import_dag_acyclic"
  | "witness_import_required"
  | "module_fingerprint_binding"
  | "telemetry_integrity"
  | "alert_on_violation"
  | "chaos_fail_closed"
  | "budget_observability"
  | "replay_resistance"
  | "mitm_resistance"
  | "forgery_resistance"
  | "dos_resistance"
  | "quarantine_policy"
  | "attack_witness"
  | "throughput_bound"
  | "latency_bound"
  | "scaling_envelope"
  | "perf_witness"
  | "resource_ceiling"
  | "reproducible_build"
  | "sbom_integrity"
  | "provenance_chain"
  | "release_signature"
  | "policy_enforced"
  | "compute_bound"
  | "energy_bound"
  | "ml2p_energy_units_joules"
  | "ml2p_esml_locality"
  | "ml2p_hardware_portability"
  | "ml2p_lifecycle_accounting"
  | "ml2p_objective_tradeoff"
  | "ml2p_power_first_class"
  | "ml2p_predictor_validation"
  | "un_symmetry_invariance"
  | "un_program_conservation"
  | "un_witnessability"
  | "un_compositionality"
  | "un_window_measure"
  | "pss_endofunctor_contract"
  | "pss_fixed_point_witness"
  | "pss_hrf_minimality"
  | "pss_hilbert_axioms"
  | "pss_unitary_evolution"
  | "pss_formal_proof"
  | "rh_constant_bank_consistency"
  | "rh_acceptance_predicate"
  | "rh_mirror_involution"
  | "rh_mirror_fixed_locus"
  | "rh_alignment_determinism"
  | "rh_alignment_tolerance"
  | "rh_skew_witness"
  | "rh_field7_gateway";

const ALLOWLIST: Invariant[] = [
  "page_conservation",
  "cycle_conservation",
  "resonance_classification",
  "holographic_correspondence",
  "budget_algebra",
  "proof_composition",
  "attestation_integrity",
  "boundary_proof",
  "witness_required",
  "signature_binding",
  "uor_identity",
  "roundtrip_preservation",
  "fixture_conformance",
  "ctp96_contract",
  "replay_protection",
  "runtime_contract",
  "local_verification",
  "resource_budget",
  "sandbox_integrity",
  "snapshot_integrity",
  "delta_proof",
  "ledger_append_only",
  "gc_safety",
  "accumulator_integrity",
  "inclusion_proof",
  "exclusion_proof",
  "cross_shard_consistency",
  "semver_backward_compat",
  "import_dag_acyclic",
  "witness_import_required",
  "module_fingerprint_binding",
  "telemetry_integrity",
  "alert_on_violation",
  "chaos_fail_closed",
  "budget_observability",
  "replay_resistance",
  "mitm_resistance",
  "forgery_resistance",
  "dos_resistance",
  "quarantine_policy",
  "attack_witness",
  "throughput_bound",
  "latency_bound",
  "scaling_envelope",
  "perf_witness",
  "resource_ceiling",
  "reproducible_build",
  "sbom_integrity",
  "provenance_chain",
  "release_signature",
  "policy_enforced",
  "compute_bound",
  "energy_bound",
  "ml2p_energy_units_joules",
  "ml2p_esml_locality",
  "ml2p_hardware_portability",
  "ml2p_lifecycle_accounting",
  "ml2p_objective_tradeoff",
  "ml2p_power_first_class",
  "ml2p_predictor_validation",
  "un_symmetry_invariance",
  "un_program_conservation",
  "un_witnessability",
  "un_compositionality",
  "un_window_measure",
  "pss_endofunctor_contract",
  "pss_fixed_point_witness",
  "pss_hrf_minimality",
  "pss_hilbert_axioms",
  "pss_unitary_evolution",
  "pss_formal_proof",
  "rh_constant_bank_consistency",
  "rh_acceptance_predicate",
  "rh_mirror_involution",
  "rh_mirror_fixed_locus",
  "rh_alignment_determinism",
  "rh_alignment_tolerance",
  "rh_skew_witness",
  "rh_field7_gateway",
];

export class InvariantChecker {
  static assertValid(list: string[]): void {
    if (!Array.isArray(list) || list.length === 0) {
      throw new Error("Invariant list must be a non-empty array");
    }
    for (const inv of list) {
      if (!ALLOWLIST.includes(inv as Invariant)) {
        throw new Error(`Unknown invariant: ${inv}`);
      }
    }
  }

  static checksum(list: string[]): string {
    // Deterministic fingerprint (sorted)
    const s = [...list].sort().join("|");
    return crypto.createHash("sha256").update(s).digest("hex");
  }

  static verifyUNInvariant(invariant: string, moduleDescriptor: any): boolean {
    const unInvariants = [
      "un_symmetry_invariance",
      "un_program_conservation", 
      "un_witnessability",
      "un_compositionality",
      "un_window_measure"
    ];
    
    if (!unInvariants.includes(invariant)) {
      return true; // Not a UN invariant, skip
    }
    
    // Fail-closed: any UN module must self-verify its contract basics
    if (!verifyUNModuleContract(moduleDescriptor)) {
      throw new Error(`UN: malformed contract for ${moduleDescriptor?.name || "<module>"}`);
    }
    
    // Optionally: ensure declared programs ⊆ admissible set for driver
    if (invariant === "un_program_conservation") {
      // Additional validation could be added here to check declared programs
      // against driver's admissible programs set
    }
    
    return true;
  }

  static verifyPSSInvariant(invariant: string, moduleDescriptor: any): boolean {
    const pssInvariants = [
      "pss_endofunctor_contract",
      "pss_fixed_point_witness",
      "pss_hrf_minimality",
      "pss_hilbert_axioms",
      "pss_unitary_evolution",
      "pss_formal_proof"
    ];
    
    if (!pssInvariants.includes(invariant)) {
      return true; // Not a PSS invariant, skip
    }
    
    // Fail-closed: delegate to PSS verifier
    const ok = verifyPSSInvariant(invariant as any, moduleDescriptor);
    if (!ok) {
      throw new Error(`PSS invariant failed: ${invariant} @ ${moduleDescriptor?.name ?? "<module>"} — see src/prime/Verifier.ts for conditions`);
    }
    
    return true;
  }

  static verifyRHInvariant(invariant: string, moduleDescriptor: any): boolean {
    const rhInvariants = [
      "rh_constant_bank_consistency",
      "rh_acceptance_predicate",
      "rh_mirror_involution",
      "rh_mirror_fixed_locus",
      "rh_alignment_determinism",
      "rh_alignment_tolerance",
      "rh_skew_witness",
      "rh_field7_gateway"
    ];
    
    if (!rhInvariants.includes(invariant)) {
      return true; // Not an RH invariant, skip
    }
    
    // Fail-closed: delegate to RH verifier
    const ok = verifyRHInvariant(invariant as any);
    if (!ok) {
      throw new Error(`RH invariant failed: ${invariant} @ ${moduleDescriptor?.name ?? "<module>"}`);
    }
    
    return true;
  }

  static verifyML2PInvariant(invariant: string, moduleDescriptor: any): boolean {
    const ml2pInvariants = [
      "ml2p_energy_units_joules",
      "ml2p_esml_locality",
      "ml2p_hardware_portability",
      "ml2p_lifecycle_accounting",
      "ml2p_objective_tradeoff",
      "ml2p_power_first_class",
      "ml2p_predictor_validation"
    ];
    
    if (!ml2pInvariants.includes(invariant)) {
      return true; // Not an ML2P invariant, skip
    }
    
    // Fail-closed: delegate to ML2P verifier
    const ok = verifyML2PInvariant(invariant as any);
    if (!ok) {
      throw new Error(`ML2P invariant failed: ${invariant} @ ${moduleDescriptor?.name ?? "<module>"}`);
    }
    
    return true;
  }
}

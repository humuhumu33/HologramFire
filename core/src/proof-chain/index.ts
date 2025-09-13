/**
 * Proof Chain System
 * 
 * Provides comprehensive proof generation, verification, and provenance tracking
 * for all computing and data transformation operations in the hologram system.
 * 
 * Features:
 * - Atomic traceability of all operations
 * - Chain of proof verification
 * - Data transformation proofs
 * - Computation proofs
 * - Monitoring and compliance tools
 * - Easy-to-use API
 */

// Core proof chain infrastructure
export { ProofChainManager } from "./ProofChain";
export type {
  ProofNode,
  ProofMetadata,
  ResourceUsage,
  ProofChain,
  ChainIntegrity,
  ProofChainResult,
  VerificationResult
} from "./ProofChain";

// Data transformation proofs
export { DataTransformationProofSystem } from "./DataTransformationProofs";
export type {
  DataTransformation,
  TransformationMetadata,
  PerformanceMetrics,
  TransformationProof
} from "./DataTransformationProofs";

// Computation proofs
export { ComputationProofSystem } from "./ComputationProofs";
export type {
  Computation,
  ComputationParameters,
  ComputationMetadata,
  ComputationPerformanceMetrics,
  MathematicalProperties,
  ComputationProof
} from "./ComputationProofs";

// Monitoring and compliance
export { ProofChainMonitor } from "./ProofChainMonitor";
export type {
  MonitoringConfig,
  AlertThresholds,
  ComplianceRule,
  MonitoringAlert,
  ComplianceReport,
  ComplianceViolation,
  ChainIntegrityReport,
  ProvenanceIntegrityReport,
  ProvenanceTrace
} from "./ProofChainMonitor";

// Easy-to-use API
export { 
  ProofChainAPI,
  createProofChainAPI,
  withProof,
  verifyChain,
  traceProvenance
} from "./ProofChainAPI";
export type {
  ProofChainAPIConfig,
  OperationResult,
  ChainVerificationResult,
  ProvenanceVerificationResult
} from "./ProofChainAPI";

// Hologram integration
export { 
  HologramProofChainIntegration,
  withHolographicProof,
  createHologramProofChainIntegration
} from "./integration/HologramProofChainIntegration";

// CLI tools
export { ProofChainCLI } from "./cli/ProofChainCLI";

// Examples
export * from "./examples/ProofChainExamples";

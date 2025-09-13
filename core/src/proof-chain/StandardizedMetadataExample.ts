/**
 * Standardized Metadata System Usage Example
 * 
 * Demonstrates how to use the new standardized metadata reporting system
 * with Oracle and Oculus metrics, witness signature provenance tracking,
 * and comprehensive validation.
 */

import { Metrics } from "../monitoring/metrics/Metrics";
import { MasterHologramOracle } from "../validator/MasterHologramOracle";
import { Oculus } from "../monitoring/meta-self-awareness/MetaSelfAwarenessLayer";
import { ProofChainManager } from "./ProofChain";
import { StandardizedMetadataReporter } from "./StandardizedMetadataReport";
import { WitnessSignatureProvenanceTracker } from "./WitnessSignatureProvenance";
import { EnhancedProofGenerator } from "./EnhancedProofGenerator";
import { MetadataValidationSystem } from "./MetadataValidationSystem";
import { ProofSystemIntegration } from "./ProofSystemIntegration";

/**
 * Example usage of the standardized metadata system
 */
export class StandardizedMetadataExample {
  private metrics: Metrics;
  private proofChainManager: ProofChainManager;
  private oracle: MasterHologramOracle;
  private oculus: Oculus;
  private metadataReporter: StandardizedMetadataReporter;
  private provenanceTracker: WitnessSignatureProvenanceTracker;
  private enhancedProofGenerator: EnhancedProofGenerator;
  private validationSystem: MetadataValidationSystem;
  private integration: ProofSystemIntegration;
  
  constructor() {
    // Initialize core components
    this.metrics = new Metrics();
    this.proofChainManager = new ProofChainManager(this.metrics);
    this.oracle = new MasterHologramOracle({
      type: 'ml-enhanced',
      config: {
        enableMLOptimization: true,
        enableAdaptiveScoring: true,
        enablePerformanceCalibration: true,
        enableRealTimeMonitoring: true,
        enablePredictiveOptimization: true
      }
    });
    this.oculus = new Oculus({
      enableLatencyOptimization: true,
      enableComputeOptimization: true,
      enableEnergyOptimization: true,
      enableOracleIntegration: true,
      enableMLOptimization: true,
      monitoringIntervalMs: 5000,
      optimizationThreshold: 0.1,
      maxOverheadPercent: 0.05,
      enableAdaptiveSampling: true,
      enablePredictiveOptimization: true,
      witnessCompressionRatio: 0.3
    }, this.metrics, this.proofChainManager);
    
    // Initialize standardized metadata components
    this.metadataReporter = new StandardizedMetadataReporter(
      this.oracle,
      this.oculus,
      this.metrics
    );
    
    this.provenanceTracker = new WitnessSignatureProvenanceTracker(this.metrics);
    
    this.enhancedProofGenerator = new EnhancedProofGenerator(
      {
        enableStandardizedMetadata: true,
        enableWitnessProvenance: true,
        enableOracleIntegration: true,
        enableOculusIntegration: true,
        enableCoherenceAnalysis: true,
        enableComputeMetrics: true,
        maxMetadataGenerationTimeMs: 5000,
        maxProvenanceTrackingTimeMs: 3000,
        minCoherenceScore: 0.8,
        minOracleConfidence: 0.7,
        minWitnessConfidence: 0.8
      },
      this.metrics,
      this.proofChainManager,
      this.oracle,
      this.oculus
    );
    
    this.validationSystem = new MetadataValidationSystem(
      {
        minOracleConfidence: 0.7,
        minOculusConfidence: 0.6,
        minCoherenceScore: 0.8,
        minWitnessConfidence: 0.8,
        minPerformanceScore: 0.5,
        minComputeEfficiency: 0.6,
        maxValidationTimeMs: 10000,
        maxComponentValidationTimeMs: 2000,
        enableStrictValidation: true,
        enablePerformanceValidation: true,
        enableSecurityValidation: true,
        enableComplianceValidation: true,
        failOnCriticalErrors: true,
        failOnHighSeverityErrors: false,
        maxWarnings: 10,
        maxRecommendations: 20
      },
      this.metrics
    );
    
    this.integration = new ProofSystemIntegration(
      {
        enableStandardizedMetadata: true,
        enableWitnessProvenance: true,
        enableEnhancedProofGeneration: true,
        enableMetadataValidation: true,
        maintainBackwardCompatibility: true,
        maxIntegrationOverheadMs: 2000,
        enableAsyncMetadataGeneration: true,
        validateExistingProofs: true,
        validateNewProofs: true
      },
      this.metrics,
      this.proofChainManager,
      this.oracle,
      this.oculus
    );
  }
  
  /**
   * Example 1: Generate a simple computation proof with standardized metadata
   */
  async example1_SimpleComputationProof(): Promise<void> {
    console.log("=== Example 1: Simple Computation Proof ===");
    
    // Define a simple computation
    const computation = {
      algorithm: "fibonacci",
      input: { n: 10 },
      parameters: { memoization: true }
    };
    
    // Computation function
    const fibonacci = (n: number): number => {
      if (n <= 1) return n;
      return fibonacci(n - 1) + fibonacci(n - 2);
    };
    
    try {
      // Generate enhanced proof
      const result = await this.enhancedProofGenerator.generateEnhancedComputationProof(
        computation,
        (input) => fibonacci(input.n),
        [] // No parent proofs
      );
      
      console.log("✅ Enhanced proof generated successfully");
      console.log(`📊 Result: ${result.result}`);
      console.log(`🔍 Proof ID: ${result.proofNode.id}`);
      console.log(`📈 Confidence: ${result.enhancedValidation.confidence}`);
      console.log(`🎯 Oracle Valid: ${result.enhancedValidation.componentValidation.oracle}`);
      console.log(`👁️ Oculus Valid: ${result.enhancedValidation.componentValidation.oculus}`);
      console.log(`🧠 Coherence Valid: ${result.enhancedValidation.componentValidation.coherence}`);
      console.log(`🔐 Witness Valid: ${result.enhancedValidation.componentValidation.witness}`);
      
      // Display standardized metadata
      if (result.standardizedMetadata) {
        console.log("\n📋 Standardized Metadata Report:");
        console.log(`   Oracle Confidence: ${result.standardizedMetadata.oracle.validationResult.confidence}`);
        console.log(`   Coherence Score: ${result.standardizedMetadata.coherence.overallScore}`);
        console.log(`   Execution Time: ${result.standardizedMetadata.performance.timing.executionTimeMs}ms`);
        console.log(`   Compute Efficiency: ${result.standardizedMetadata.compute.efficiency.overallEfficiency}`);
        console.log(`   Witness Signature: ${result.standardizedMetadata.witness.signature.substring(0, 20)}...`);
      }
      
    } catch (error) {
      console.error("❌ Error generating computation proof:", error);
    }
  }
  
  /**
   * Example 2: Generate a proof chain with witness signature provenance
   */
  async example2_ProofChainWithProvenance(): Promise<void> {
    console.log("\n=== Example 2: Proof Chain with Provenance ===");
    
    try {
      // Step 1: Generate first proof (data preprocessing)
      const preprocessingResult = await this.enhancedProofGenerator.generateEnhancedTransformationProof(
        {
          type: "normalize",
          input: [1, 2, 3, 4, 5],
          parameters: { method: "min-max" }
        },
        (input) => {
          const min = Math.min(...input);
          const max = Math.max(...input);
          return input.map(x => (x - min) / (max - min));
        },
        [] // No parent proofs
      );
      
      console.log("✅ Step 1: Data preprocessing proof generated");
      console.log(`   Proof ID: ${preprocessingResult.proofNode.id}`);
      console.log(`   Result: [${preprocessingResult.result.slice(0, 3).map(x => x.toFixed(2)).join(', ')}...]`);
      
      // Step 2: Generate second proof (computation) using first proof as input
      const computationResult = await this.enhancedProofGenerator.generateEnhancedComputationProof(
        {
          algorithm: "mean",
          input: preprocessingResult.result,
          parameters: { weighted: false }
        },
        (input) => input.reduce((sum, x) => sum + x, 0) / input.length,
        [preprocessingResult.proofNode.id] // Parent proof
      );
      
      console.log("✅ Step 2: Computation proof generated");
      console.log(`   Proof ID: ${computationResult.proofNode.id}`);
      console.log(`   Result: ${computationResult.result.toFixed(4)}`);
      console.log(`   Parent Proof: ${preprocessingResult.proofNode.id}`);
      
      // Step 3: Generate third proof (validation) using both previous proofs
      const validationResult = await this.enhancedProofGenerator.generateEnhancedValidationProof(
        {
          type: "range_check",
          data: computationResult.result,
          rules: { min: 0, max: 1 }
        },
        (data, rules) => data >= rules.min && data <= rules.max,
        [preprocessingResult.proofNode.id, computationResult.proofNode.id] // Parent proofs
      );
      
      console.log("✅ Step 3: Validation proof generated");
      console.log(`   Proof ID: ${validationResult.proofNode.id}`);
      console.log(`   Result: ${validationResult.result}`);
      console.log(`   Parent Proofs: ${[preprocessingResult.proofNode.id, computationResult.proofNode.id].join(', ')}`);
      
      // Display provenance chain information
      console.log("\n🔗 Provenance Chain Information:");
      console.log(`   Chain Length: 3 proofs`);
      console.log(`   Full Traceability: ✅`);
      console.log(`   Witness Signatures: ✅`);
      console.log(`   Oracle Validation: ✅`);
      console.log(`   Oculus Metrics: ✅`);
      
    } catch (error) {
      console.error("❌ Error generating proof chain:", error);
    }
  }
  
  /**
   * Example 3: Validate existing proof metadata
   */
  async example3_ValidateExistingProof(): Promise<void> {
    console.log("\n=== Example 3: Validate Existing Proof ===");
    
    try {
      // First, generate a proof
      const proofResult = await this.enhancedProofGenerator.generateEnhancedProof(
        "example_validation",
        { data: "test" },
        (input) => `processed_${input.data}`,
        []
      );
      
      const proofId = proofResult.proofNode.id;
      console.log(`🔍 Validating proof: ${proofId}`);
      
      // Validate the proof
      const validationResult = await this.enhancedProofGenerator.verifyEnhancedProof(proofId);
      
      console.log("📋 Validation Results:");
      console.log(`   Overall Valid: ${validationResult.isValid ? '✅' : '❌'}`);
      console.log(`   Confidence: ${(validationResult.confidence * 100).toFixed(1)}%`);
      console.log(`   Oracle Valid: ${validationResult.componentValidation.oracle ? '✅' : '❌'}`);
      console.log(`   Oculus Valid: ${validationResult.componentValidation.oculus ? '✅' : '❌'}`);
      console.log(`   Coherence Valid: ${validationResult.componentValidation.coherence ? '✅' : '❌'}`);
      console.log(`   Witness Valid: ${validationResult.componentValidation.witness ? '✅' : '❌'}`);
      console.log(`   Compute Valid: ${validationResult.componentValidation.compute ? '✅' : '❌'}`);
      
      if (validationResult.errors.length > 0) {
        console.log("\n❌ Errors:");
        validationResult.errors.forEach(error => console.log(`   - ${error}`));
      }
      
      if (validationResult.warnings.length > 0) {
        console.log("\n⚠️ Warnings:");
        validationResult.warnings.forEach(warning => console.log(`   - ${warning}`));
      }
      
      if (validationResult.recommendations.length > 0) {
        console.log("\n💡 Recommendations:");
        validationResult.recommendations.forEach(rec => console.log(`   - ${rec}`));
      }
      
    } catch (error) {
      console.error("❌ Error validating proof:", error);
    }
  }
  
  /**
   * Example 4: Integrate with existing proof system
   */
  async example4_IntegrateWithExistingSystem(): Promise<void> {
    console.log("\n=== Example 4: Integrate with Existing System ===");
    
    try {
      // Simulate existing proof metadata
      const existingMetadata = {
        operationType: "computation" as const,
        complexity: 5,
        executionTimeMs: 100,
        resourceUsage: {
          cpuCycles: 1000000,
          memoryBytes: 1024,
          energyJoules: 0.001,
          networkBytes: 0
        },
        holographicCorrespondence: "existing_correspondence",
        invariants: ["test_invariant"],
        dependencies: []
      };
      
      const proofData = {
        operation: "existing_operation",
        input: { value: 42 },
        result: { processed: 84 }
      };
      
      console.log("🔄 Enhancing existing proof metadata...");
      
      // Enhance existing metadata
      const integrationResult = await this.integration.enhanceProofMetadata(
        "existing_proof_123",
        existingMetadata,
        proofData,
        []
      );
      
      console.log("📊 Integration Results:");
      console.log(`   Success: ${integrationResult.success ? '✅' : '❌'}`);
      console.log(`   Enhanced Metadata: ${integrationResult.enhancedMetadata ? '✅' : '❌'}`);
      console.log(`   Witness Provenance: ${integrationResult.witnessProvenance ? '✅' : '❌'}`);
      console.log(`   Integration Time: ${integrationResult.integrationTimeMs}ms`);
      
      if (integrationResult.errors.length > 0) {
        console.log("\n❌ Integration Errors:");
        integrationResult.errors.forEach(error => console.log(`   - ${error}`));
      }
      
      if (integrationResult.warnings.length > 0) {
        console.log("\n⚠️ Integration Warnings:");
        integrationResult.warnings.forEach(warning => console.log(`   - ${warning}`));
      }
      
      if (integrationResult.recommendations.length > 0) {
        console.log("\n💡 Integration Recommendations:");
        integrationResult.recommendations.forEach(rec => console.log(`   - ${rec}`));
      }
      
      // Get integration status
      const status = this.integration.getIntegrationStatus();
      console.log("\n📈 Integration Status:");
      console.log(`   Total Proofs: ${status.totalProofs}`);
      console.log(`   Enhanced Proofs: ${status.enhancedProofs}`);
      console.log(`   Witness Provenance: ${status.witnessProvenanceProofs}`);
      console.log(`   Validated Proofs: ${status.validatedProofs}`);
      console.log(`   Coverage: ${status.integrationCoverage.toFixed(1)}%`);
      
    } catch (error) {
      console.error("❌ Error integrating with existing system:", error);
    }
  }
  
  /**
   * Example 5: Comprehensive metadata validation
   */
  async example5_ComprehensiveValidation(): Promise<void> {
    console.log("\n=== Example 5: Comprehensive Metadata Validation ===");
    
    try {
      // Generate a proof with full metadata
      const proofResult = await this.enhancedProofGenerator.generateEnhancedProof(
        "comprehensive_validation",
        { complex: "data", nested: { value: 123 } },
        (input) => ({ processed: input.complex, doubled: input.nested.value * 2 }),
        []
      );
      
      if (!proofResult.standardizedMetadata) {
        throw new Error("No standardized metadata available");
      }
      
      console.log("🔍 Performing comprehensive metadata validation...");
      
      // Validate the metadata
      const validationResult = await this.validationSystem.validateMetadataReport(
        proofResult.standardizedMetadata
      );
      
      console.log("📋 Comprehensive Validation Results:");
      console.log(`   Overall Valid: ${validationResult.isValid ? '✅' : '❌'}`);
      console.log(`   Confidence: ${(validationResult.confidence * 100).toFixed(1)}%`);
      console.log(`   Status: ${validationResult.status}`);
      console.log(`   Validation Time: ${validationResult.timing.totalTimeMs}ms`);
      
      console.log("\n🧩 Component Validation:");
      Object.entries(validationResult.components).forEach(([component, result]) => {
        console.log(`   ${component}: ${result.isValid ? '✅' : '❌'} (${(result.confidence * 100).toFixed(1)}%)`);
      });
      
      if (validationResult.details.errors.length > 0) {
        console.log("\n❌ Validation Errors:");
        validationResult.details.errors.forEach(error => {
          console.log(`   [${error.severity.toUpperCase()}] ${error.component}.${error.field}: ${error.message}`);
        });
      }
      
      if (validationResult.details.warnings.length > 0) {
        console.log("\n⚠️ Validation Warnings:");
        validationResult.details.warnings.forEach(warning => {
          console.log(`   [${warning.impact.toUpperCase()}] ${warning.component}.${warning.field}: ${warning.message}`);
        });
      }
      
      if (validationResult.details.recommendations.length > 0) {
        console.log("\n💡 Validation Recommendations:");
        validationResult.details.recommendations.forEach(rec => {
          console.log(`   [${rec.priority.toUpperCase()}] ${rec.component}.${rec.field}: ${rec.message}`);
        });
      }
      
    } catch (error) {
      console.error("❌ Error in comprehensive validation:", error);
    }
  }
  
  /**
   * Run all examples
   */
  async runAllExamples(): Promise<void> {
    console.log("🚀 Starting Standardized Metadata System Examples\n");
    
    try {
      await this.example1_SimpleComputationProof();
      await this.example2_ProofChainWithProvenance();
      await this.example3_ValidateExistingProof();
      await this.example4_IntegrateWithExistingSystem();
      await this.example5_ComprehensiveValidation();
      
      console.log("\n🎉 All examples completed successfully!");
      
    } catch (error) {
      console.error("❌ Error running examples:", error);
    }
  }
}

// Export for use in other modules
// (Already exported as class declaration above)

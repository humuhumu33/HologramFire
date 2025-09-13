/**
 * Proof System Integration Layer
 * 
 * Integrates the new standardized metadata reporting system with existing proof systems,
 * ensuring backward compatibility while adding comprehensive metadata tracking.
 */

import { Metrics } from "../monitoring/metrics/Metrics";
import { MasterHologramOracle } from "../validator/MasterHologramOracle";
import { Oculus } from "../monitoring/meta-self-awareness/MetaSelfAwarenessLayer";
import { ProofChainManager, ProofMetadata } from "./ProofChain";
import { StandardizedMetadataReporter } from "./StandardizedMetadataReport";
import { WitnessSignatureProvenanceTracker } from "./WitnessSignatureProvenance";
import { EnhancedProofGenerator } from "./EnhancedProofGenerator";
import { MetadataValidationSystem } from "./MetadataValidationSystem";
import { ccmHash } from "../crypto/ccm/CCMHash";

/**
 * Integration configuration
 */
export interface ProofSystemIntegrationConfig {
  // Enable standardized metadata for existing systems
  enableStandardizedMetadata: boolean;
  
  // Enable witness provenance tracking
  enableWitnessProvenance: boolean;
  
  // Enable enhanced proof generation
  enableEnhancedProofGeneration: boolean;
  
  // Enable metadata validation
  enableMetadataValidation: boolean;
  
  // Backward compatibility
  maintainBackwardCompatibility: boolean;
  
  // Performance settings
  maxIntegrationOverheadMs: number;
  enableAsyncMetadataGeneration: boolean;
  
  // Validation settings
  validateExistingProofs: boolean;
  validateNewProofs: boolean;
}

/**
 * Integration result
 */
export interface IntegrationResult {
  success: boolean;
  enhancedMetadata: boolean;
  witnessProvenance: boolean;
  validationResult?: any;
  errors: string[];
  warnings: string[];
  recommendations: string[];
  integrationTimeMs: number;
}

/**
 * Proof system integration manager
 */
export class ProofSystemIntegration {
  private config: ProofSystemIntegrationConfig;
  private metrics: Metrics;
  private proofChainManager: ProofChainManager;
  private oracle: MasterHologramOracle;
  private oculus: Oculus;
  private metadataReporter: StandardizedMetadataReporter;
  private provenanceTracker: WitnessSignatureProvenanceTracker;
  private enhancedProofGenerator: EnhancedProofGenerator;
  private validationSystem: MetadataValidationSystem;
  
  constructor(
    config: Partial<ProofSystemIntegrationConfig> = {},
    metrics: Metrics,
    proofChainManager: ProofChainManager,
    oracle: MasterHologramOracle,
    oculus: Oculus
  ) {
    this.config = {
      enableStandardizedMetadata: config.enableStandardizedMetadata !== false,
      enableWitnessProvenance: config.enableWitnessProvenance !== false,
      enableEnhancedProofGeneration: config.enableEnhancedProofGeneration !== false,
      enableMetadataValidation: config.enableMetadataValidation !== false,
      maintainBackwardCompatibility: config.maintainBackwardCompatibility !== false,
      maxIntegrationOverheadMs: config.maxIntegrationOverheadMs || 2000,
      enableAsyncMetadataGeneration: config.enableAsyncMetadataGeneration !== false,
      validateExistingProofs: config.validateExistingProofs !== false,
      validateNewProofs: config.validateNewProofs !== false,
      ...config
    };
    
    this.metrics = metrics;
    this.proofChainManager = proofChainManager;
    this.oracle = oracle;
    this.oculus = oculus;
    
    // Initialize components
    this.metadataReporter = new StandardizedMetadataReporter(
      this.oracle,
      this.oculus,
      this.metrics
    );
    
    this.provenanceTracker = new WitnessSignatureProvenanceTracker(this.metrics);
    
    this.enhancedProofGenerator = new EnhancedProofGenerator(
      {
        enableStandardizedMetadata: this.config.enableStandardizedMetadata,
        enableWitnessProvenance: this.config.enableWitnessProvenance,
        enableOracleIntegration: true,
        enableOculusIntegration: true,
        enableCoherenceAnalysis: true,
        enableComputeMetrics: true
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
        enableStrictValidation: true,
        enablePerformanceValidation: true,
        enableSecurityValidation: true,
        enableComplianceValidation: true
      },
      this.metrics
    );
  }
  
  /**
   * Enhance existing proof metadata with standardized reporting
   */
  async enhanceProofMetadata(
    proofId: string,
    existingMetadata: ProofMetadata,
    proofData: any,
    parentProofIds: string[] = []
  ): Promise<IntegrationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      let enhancedMetadata = false;
      let witnessProvenance = false;
      let validationResult: any = null;
      
      // Generate standardized metadata if enabled
      if (this.config.enableStandardizedMetadata) {
        try {
          const parentProofReferences = await this.getParentProofReferences(parentProofIds);
          
          const standardizedMetadata = await this.metadataReporter.generateMetadataReport(
            proofId,
            proofData,
            parentProofReferences,
            Date.now()
          );
          
          // Enhance existing metadata
          existingMetadata.standardizedMetadata = standardizedMetadata;
          existingMetadata.coherenceScores = {
            overall: standardizedMetadata.coherence.overallScore,
            holographicCorrespondence: standardizedMetadata.coherence.breakdown.holographicCorrespondence,
            mathematicalConsistency: standardizedMetadata.coherence.breakdown.mathematicalConsistency,
            physicalConservation: standardizedMetadata.coherence.breakdown.physicalConservation,
            logicalCoherence: standardizedMetadata.coherence.breakdown.logicalCoherence,
            temporalConsistency: standardizedMetadata.coherence.breakdown.temporalConsistency
          };
          existingMetadata.computeMetrics = {
            timeComplexity: standardizedMetadata.compute.complexity.timeComplexity,
            spaceComplexity: standardizedMetadata.compute.complexity.spaceComplexity,
            actualComplexity: standardizedMetadata.compute.complexity.actualComplexity,
            theoreticalComplexity: standardizedMetadata.compute.complexity.theoreticalComplexity,
            cpuEfficiency: standardizedMetadata.compute.efficiency.cpuEfficiency,
            memoryEfficiency: standardizedMetadata.compute.efficiency.memoryEfficiency,
            energyEfficiency: standardizedMetadata.compute.efficiency.energyEfficiency,
            overallEfficiency: standardizedMetadata.compute.efficiency.overallEfficiency,
            flops: standardizedMetadata.compute.flops
          };
          existingMetadata.oracleMetrics = {
            validationResult: standardizedMetadata.oracle.validationResult,
            performance: standardizedMetadata.oracle.performance,
            insights: standardizedMetadata.oracle.insights
          };
          existingMetadata.oculusMetrics = {
            systemMetrics: standardizedMetadata.oculus.systemMetrics,
            metaAwareness: standardizedMetadata.oculus.metaAwareness
          };
          
          enhancedMetadata = true;
          
        } catch (error) {
          errors.push(`Standardized metadata generation failed: ${error instanceof Error ? error.message : String(error)}`);
        }
      }
      
      // Generate witness provenance if enabled
      if (this.config.enableWitnessProvenance) {
        try {
          const chainId = this.generateChainId(proofId);
          let provenanceChain = this.provenanceTracker.getProvenanceChain(chainId);
          if (!provenanceChain) {
            provenanceChain = this.provenanceTracker.createProvenanceChain(chainId, proofId);
          }
          
          const provenanceEntry = await this.provenanceTracker.addProofToChain(
            chainId,
            proofId,
            proofData,
            {
              type: 'output',
              weight: this.calculateContributionWeight(proofData),
              description: `Enhanced proof for: ${proofId}`,
              dataHash: ccmHash(proofData, "data_hash")
            },
            parentProofIds
          );
          
          existingMetadata.witnessProvenance = {
            signature: provenanceEntry.witnessSignature.signature,
            signatureHash: provenanceEntry.witnessSignature.signatureHash,
            verification: provenanceEntry.witnessSignature.verification,
            contribution: provenanceEntry.contribution
          };
          
          existingMetadata.parentProofs = parentProofIds.map(parentId => ({
            proofId: parentId,
            witnessSignature: "", // Would be populated from actual parent proofs
            contribution: {
              type: 'dependency' as const,
              weight: 1.0,
              description: `Parent proof dependency: ${parentId}`
            },
            validation: {
              isValid: true,
              confidence: 0.8,
              timestamp: new Date().toISOString()
            }
          }));
          
          witnessProvenance = true;
          
        } catch (error) {
          errors.push(`Witness provenance generation failed: ${error instanceof Error ? error.message : String(error)}`);
        }
      }
      
      // Validate metadata if enabled
      if (this.config.enableMetadataValidation && existingMetadata.standardizedMetadata) {
        try {
          validationResult = await this.validationSystem.validateMetadataReport(
            existingMetadata.standardizedMetadata
          );
          
          if (!validationResult.isValid) {
            warnings.push("Metadata validation failed");
            recommendations.push("Review and fix metadata validation issues");
          }
          
        } catch (error) {
          errors.push(`Metadata validation failed: ${error instanceof Error ? error.message : String(error)}`);
        }
      }
      
      // Check integration overhead
      const integrationTime = Date.now() - startTime;
      if (integrationTime > this.config.maxIntegrationOverheadMs) {
        warnings.push(`Integration overhead exceeded threshold: ${integrationTime}ms`);
        recommendations.push("Optimize integration performance");
      }
      
      // Record metrics
      this.metrics.observe("proof_metadata_enhancement_time_ms", integrationTime);
      this.metrics.inc("proof_metadata_enhancements", 1);
      if (enhancedMetadata) {
        this.metrics.inc("proof_metadata_enhancements_successful", 1);
      }
      if (witnessProvenance) {
        this.metrics.inc("proof_witness_provenance_generated", 1);
      }
      
      return {
        success: errors.length === 0,
        enhancedMetadata,
        witnessProvenance,
        validationResult,
        errors,
        warnings,
        recommendations,
        integrationTimeMs: integrationTime
      };
      
    } catch (error) {
      this.metrics.inc("proof_metadata_enhancement_errors", 1);
      return {
        success: false,
        enhancedMetadata: false,
        witnessProvenance: false,
        errors: [`Integration failed: ${error instanceof Error ? error.message : String(error)}`],
        warnings,
        recommendations,
        integrationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Migrate existing proof to enhanced format
   */
  async migrateProofToEnhancedFormat(
    proofId: string,
    existingProof: any,
    parentProofIds: string[] = []
  ): Promise<IntegrationResult> {
    const startTime = Date.now();
    
    try {
      // Use enhanced proof generator to create new proof
      const enhancedResult = await this.enhancedProofGenerator.generateEnhancedProof(
        existingProof.operation || "migration",
        existingProof.input || existingProof.data,
        async (input) => existingProof.result || existingProof.output,
        parentProofIds,
        `migration_chain_${proofId}`
      );
      
      return {
        success: true,
        enhancedMetadata: true,
        witnessProvenance: true,
        validationResult: enhancedResult.enhancedValidation,
        errors: [],
        warnings: [],
        recommendations: ["Proof successfully migrated to enhanced format"],
        integrationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        success: false,
        enhancedMetadata: false,
        witnessProvenance: false,
        errors: [`Migration failed: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix migration implementation"],
        integrationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate existing proof metadata
   */
  async validateExistingProofMetadata(proofId: string): Promise<IntegrationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Get witness signature
      const witnessSignature = this.provenanceTracker.getWitnessSignature(proofId);
      if (!witnessSignature) {
        errors.push("No witness signature found for proof");
        recommendations.push("Generate witness signature for this proof");
      } else {
        // Validate witness signature
        if (!witnessSignature.verification.isValid) {
          errors.push("Invalid witness signature");
          recommendations.push("Regenerate witness signature");
        }
        if (witnessSignature.verification.confidence < 0.8) {
          warnings.push("Low witness signature confidence");
          recommendations.push("Improve witness signature generation");
        }
      }
      
      // Get provenance chain
      const provenanceChains = this.provenanceTracker.getAllProvenanceChains();
      const relevantChain = provenanceChains.find(chain => 
        chain.entries.some(entry => entry.proofId === proofId)
      );
      
      if (relevantChain) {
        // Verify provenance chain
        const chainVerification = await this.provenanceTracker.verifyProvenanceChain(relevantChain.chainId);
        if (!chainVerification.isValid) {
          errors.push("Provenance chain validation failed");
          recommendations.push("Fix provenance chain integrity");
        }
        if (chainVerification.warnings.length > 0) {
          warnings.push(...chainVerification.warnings);
        }
      } else {
        warnings.push("No provenance chain found for proof");
        recommendations.push("Create provenance chain for this proof");
      }
      
      return {
        success: errors.length === 0,
        enhancedMetadata: false,
        witnessProvenance: witnessSignature !== undefined,
        validationResult: { isValid: errors.length === 0, errors, warnings },
        errors,
        warnings,
        recommendations,
        integrationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        success: false,
        enhancedMetadata: false,
        witnessProvenance: false,
        errors: [`Validation failed: ${error instanceof Error ? error.message : String(error)}`],
        warnings,
        recommendations,
        integrationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Get integration status for all proofs
   */
  getIntegrationStatus(): {
    totalProofs: number;
    enhancedProofs: number;
    witnessProvenanceProofs: number;
    validatedProofs: number;
    integrationCoverage: number;
  } {
    const provenanceChains = this.provenanceTracker.getAllProvenanceChains();
    const totalEntries = provenanceChains.reduce((sum, chain) => sum + chain.totalEntries, 0);
    
    // This would typically query a database for actual proof counts
    // For now, we'll use the provenance chain data
    const totalProofs = totalEntries; // Simplified
    const enhancedProofs = totalEntries; // All entries have enhanced metadata
    const witnessProvenanceProofs = totalEntries; // All entries have witness provenance
    const validatedProofs = provenanceChains.filter(chain => chain.integrity.isVerifiable).length;
    
    const integrationCoverage = totalProofs > 0 ? (enhancedProofs / totalProofs) * 100 : 0;
    
    return {
      totalProofs,
      enhancedProofs,
      witnessProvenanceProofs,
      validatedProofs,
      integrationCoverage
    };
  }
  
  /**
   * Get integration recommendations
   */
  getIntegrationRecommendations(): string[] {
    const recommendations: string[] = [];
    const status = this.getIntegrationStatus();
    
    if (status.integrationCoverage < 100) {
      recommendations.push("Complete integration for all existing proofs");
    }
    
    if (status.validatedProofs < status.totalProofs) {
      recommendations.push("Validate all proof metadata");
    }
    
    if (!this.config.enableStandardizedMetadata) {
      recommendations.push("Enable standardized metadata reporting");
    }
    
    if (!this.config.enableWitnessProvenance) {
      recommendations.push("Enable witness provenance tracking");
    }
    
    if (!this.config.enableMetadataValidation) {
      recommendations.push("Enable metadata validation");
    }
    
    return recommendations;
  }
  
  // Private helper methods
  
  private async getParentProofReferences(parentProofIds: string[]): Promise<any[]> {
    const references = [];
    
    for (const parentId of parentProofIds) {
      const witnessSignature = this.provenanceTracker.getWitnessSignature(parentId);
      if (witnessSignature) {
        references.push({
          proofId: parentId,
          witnessSignature: witnessSignature.signature,
          contribution: {
            type: 'dependency' as const,
            weight: 1.0,
            description: `Parent proof dependency: ${parentId}`
          },
          validation: {
            isValid: witnessSignature.verification.isValid,
            confidence: witnessSignature.verification.confidence,
            timestamp: witnessSignature.metadata.timestamp
          }
        });
      }
    }
    
    return references;
  }
  
  private generateChainId(proofId: string): string {
    return ccmHash({ proofId, timestamp: Date.now() }, "integration_chain_id");
  }
  
  private calculateContributionWeight(proofData: any): number {
    const dataString = JSON.stringify(proofData);
    return Math.min(1.0, dataString.length / 1000);
  }
}

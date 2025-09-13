/**
 * Metadata Validation and Verification System
 * 
 * Provides comprehensive validation and verification of standardized metadata reports,
 * ensuring data integrity, consistency, and compliance with system requirements.
 */

import { Metrics } from "../monitoring/metrics/Metrics";
import { StandardizedMetadataReport } from "./StandardizedMetadataReport";
import { WitnessSignature } from "./WitnessSignatureProvenance";
import { ccmHash } from "../crypto/ccm/CCMHash";

/**
 * Validation result for metadata components
 */
export interface MetadataValidationResult {
  // Overall validation status
  isValid: boolean;
  confidence: number;
  status: 'valid' | 'invalid' | 'warning' | 'error';
  
  // Component validation results
  components: {
    oracle: ComponentValidationResult;
    oculus: ComponentValidationResult;
    coherence: ComponentValidationResult;
    performance: ComponentValidationResult;
    compute: ComponentValidationResult;
    provenance: ComponentValidationResult;
    witness: ComponentValidationResult;
    holographic: ComponentValidationResult;
  };
  
  // Validation details
  details: {
    errors: ValidationError[];
    warnings: ValidationWarning[];
    recommendations: ValidationRecommendation[];
  };
  
  // Validation timing
  timing: {
    totalTimeMs: number;
    oracleTimeMs: number;
    oculusTimeMs: number;
    coherenceTimeMs: number;
    performanceTimeMs: number;
    computeTimeMs: number;
    provenanceTimeMs: number;
    witnessTimeMs: number;
    holographicTimeMs: number;
  };
  
  // Validation metadata
  metadata: {
    validator: string;
    version: string;
    timestamp: string;
    validationId: string;
  };
}

/**
 * Component validation result
 */
export interface ComponentValidationResult {
  isValid: boolean;
  confidence: number;
  score: number;
  errors: string[];
  warnings: string[];
  recommendations: string[];
  validationTimeMs: number;
}

/**
 * Validation error
 */
export interface ValidationError {
  component: string;
  field: string;
  code: string;
  message: string;
  severity: 'critical' | 'high' | 'medium' | 'low';
  timestamp: string;
}

/**
 * Validation warning
 */
export interface ValidationWarning {
  component: string;
  field: string;
  code: string;
  message: string;
  impact: 'performance' | 'security' | 'reliability' | 'compliance';
  timestamp: string;
}

/**
 * Validation recommendation
 */
export interface ValidationRecommendation {
  component: string;
  field: string;
  code: string;
  message: string;
  priority: 'high' | 'medium' | 'low';
  action: string;
  timestamp: string;
}

/**
 * Validation configuration
 */
export interface ValidationConfig {
  // Validation thresholds
  minOracleConfidence: number;
  minOculusConfidence: number;
  minCoherenceScore: number;
  minWitnessConfidence: number;
  minPerformanceScore: number;
  minComputeEfficiency: number;
  
  // Validation timeouts
  maxValidationTimeMs: number;
  maxComponentValidationTimeMs: number;
  
  // Validation options
  enableStrictValidation: boolean;
  enablePerformanceValidation: boolean;
  enableSecurityValidation: boolean;
  enableComplianceValidation: boolean;
  
  // Error handling
  failOnCriticalErrors: boolean;
  failOnHighSeverityErrors: boolean;
  maxWarnings: number;
  maxRecommendations: number;
}

/**
 * Metadata validation system
 */
export class MetadataValidationSystem {
  private config: ValidationConfig;
  private metrics: Metrics;
  
  constructor(
    config: Partial<ValidationConfig> = {},
    metrics: Metrics
  ) {
    this.config = {
      minOracleConfidence: config.minOracleConfidence || 0.7,
      minOculusConfidence: config.minOculusConfidence || 0.6,
      minCoherenceScore: config.minCoherenceScore || 0.8,
      minWitnessConfidence: config.minWitnessConfidence || 0.8,
      minPerformanceScore: config.minPerformanceScore || 0.5,
      minComputeEfficiency: config.minComputeEfficiency || 0.6,
      maxValidationTimeMs: config.maxValidationTimeMs || 10000,
      maxComponentValidationTimeMs: config.maxComponentValidationTimeMs || 2000,
      enableStrictValidation: config.enableStrictValidation !== false,
      enablePerformanceValidation: config.enablePerformanceValidation !== false,
      enableSecurityValidation: config.enableSecurityValidation !== false,
      enableComplianceValidation: config.enableComplianceValidation !== false,
      failOnCriticalErrors: config.failOnCriticalErrors !== false,
      failOnHighSeverityErrors: config.failOnHighSeverityErrors !== false,
      maxWarnings: config.maxWarnings || 10,
      maxRecommendations: config.maxRecommendations || 20,
      ...config
    };
    
    this.metrics = metrics;
  }
  
  /**
   * Validate a standardized metadata report
   */
  async validateMetadataReport(
    metadataReport: StandardizedMetadataReport
  ): Promise<MetadataValidationResult> {
    const startTime = Date.now();
    const validationId = this.generateValidationId();
    
    try {
      // Validate each component
      const oracleResult = await this.validateOracleMetrics(metadataReport.oracle);
      const oculusResult = await this.validateOculusMetrics(metadataReport.oculus);
      const coherenceResult = await this.validateCoherenceAnalysis(metadataReport.coherence);
      const performanceResult = await this.validatePerformanceMetrics(metadataReport.performance);
      const computeResult = await this.validateComputeMetrics(metadataReport.compute);
      const provenanceResult = await this.validateProvenanceChain(metadataReport.provenance);
      const witnessResult = await this.validateWitnessVerification(metadataReport.witness);
      const holographicResult = await this.validateHolographicCorrespondence(metadataReport);
      
      // Aggregate validation results
      const components = {
        oracle: oracleResult,
        oculus: oculusResult,
        coherence: coherenceResult,
        performance: performanceResult,
        compute: computeResult,
        provenance: provenanceResult,
        witness: witnessResult,
        holographic: holographicResult
      };
      
      // Calculate overall validation status
      const overallValidation = this.calculateOverallValidation(components);
      
      // Collect all errors, warnings, and recommendations
      const details = this.collectValidationDetails(components);
      
      // Create validation result
      const result: MetadataValidationResult = {
        isValid: overallValidation.isValid,
        confidence: overallValidation.confidence,
        status: overallValidation.status,
        components,
        details,
        timing: {
          totalTimeMs: Date.now() - startTime,
          oracleTimeMs: oracleResult.validationTimeMs,
          oculusTimeMs: oculusResult.validationTimeMs,
          coherenceTimeMs: coherenceResult.validationTimeMs,
          performanceTimeMs: performanceResult.validationTimeMs,
          computeTimeMs: computeResult.validationTimeMs,
          provenanceTimeMs: provenanceResult.validationTimeMs,
          witnessTimeMs: witnessResult.validationTimeMs,
          holographicTimeMs: holographicResult.validationTimeMs
        },
        metadata: {
          validator: "MetadataValidationSystem",
          version: "1.0.0",
          timestamp: new Date().toISOString(),
          validationId
        }
      };
      
      // Record metrics
      this.metrics.observe("metadata_validation_time_ms", result.timing.totalTimeMs);
      this.metrics.inc("metadata_validations", 1);
      if (result.isValid) {
        this.metrics.inc("metadata_validations_valid", 1);
      } else {
        this.metrics.inc("metadata_validations_invalid", 1);
      }
      
      return result;
      
    } catch (error) {
      this.metrics.inc("metadata_validation_errors", 1);
      throw new Error(`Metadata validation failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
  
  /**
   * Validate Oracle metrics
   */
  private async validateOracleMetrics(oracleMetrics: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate validation result
      if (!oracleMetrics.validationResult) {
        errors.push("Missing Oracle validation result");
      } else {
        if (!oracleMetrics.validationResult.isValid) {
          errors.push("Oracle validation failed");
        }
        if (oracleMetrics.validationResult.confidence < this.config.minOracleConfidence) {
          warnings.push(`Oracle confidence below threshold: ${oracleMetrics.validationResult.confidence}`);
          recommendations.push("Improve Oracle validation accuracy");
        }
        if (oracleMetrics.validationResult.violations && oracleMetrics.validationResult.violations.length > 0) {
          errors.push(`Oracle violations: ${oracleMetrics.validationResult.violations.join(', ')}`);
        }
      }
      
      // Validate performance metrics
      if (!oracleMetrics.performance) {
        errors.push("Missing Oracle performance metrics");
      } else {
        if (oracleMetrics.performance.totalTimeMs > this.config.maxComponentValidationTimeMs) {
          warnings.push("Oracle validation took too long");
          recommendations.push("Optimize Oracle performance");
        }
        if (oracleMetrics.performance.memoryUsageBytes > 100000000) { // 100MB
          warnings.push("High Oracle memory usage");
          recommendations.push("Optimize Oracle memory usage");
        }
      }
      
      // Validate insights
      if (!oracleMetrics.insights) {
        errors.push("Missing Oracle insights");
      } else {
        if (oracleMetrics.insights.complexity < 0 || oracleMetrics.insights.complexity > 1) {
          errors.push("Invalid Oracle complexity score");
        }
        if (oracleMetrics.insights.stability < 0.5) {
          warnings.push("Low Oracle stability score");
          recommendations.push("Improve system stability");
        }
        if (oracleMetrics.insights.efficiency < 0.5) {
          warnings.push("Low Oracle efficiency score");
          recommendations.push("Improve system efficiency");
        }
      }
      
      // Validate fingerprint
      if (!oracleMetrics.fingerprint || oracleMetrics.fingerprint.length === 0) {
        errors.push("Missing Oracle fingerprint");
      }
      
      // Validate holographic correspondence
      if (!oracleMetrics.holographicCorrespondence || oracleMetrics.holographicCorrespondence.length === 0) {
        errors.push("Missing Oracle holographic correspondence");
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (oracleMetrics.validationResult?.confidence || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Oracle validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix Oracle validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate Oculus metrics
   */
  private async validateOculusMetrics(oculusMetrics: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate system metrics
      if (!oculusMetrics.systemMetrics) {
        errors.push("Missing Oculus system metrics");
      } else {
        // Validate latency metrics
        if (!oculusMetrics.systemMetrics.latency) {
          errors.push("Missing Oculus latency metrics");
        } else {
          if (oculusMetrics.systemMetrics.latency.average > 1000) { // 1 second
            warnings.push("High average latency");
            recommendations.push("Optimize system latency");
          }
          if (oculusMetrics.systemMetrics.latency.p99 > 5000) { // 5 seconds
            warnings.push("High P99 latency");
            recommendations.push("Optimize system performance");
          }
        }
        
        // Validate compute metrics
        if (!oculusMetrics.systemMetrics.compute) {
          errors.push("Missing Oculus compute metrics");
        } else {
          if (oculusMetrics.systemMetrics.compute.cpuUtilization > 0.9) {
            warnings.push("High CPU utilization");
            recommendations.push("Optimize CPU usage");
          }
          if (oculusMetrics.systemMetrics.compute.memoryUtilization > 0.9) {
            warnings.push("High memory utilization");
            recommendations.push("Optimize memory usage");
          }
          if (oculusMetrics.systemMetrics.compute.efficiency < this.config.minOculusConfidence) {
            warnings.push("Low compute efficiency");
            recommendations.push("Improve compute efficiency");
          }
        }
        
        // Validate energy metrics
        if (!oculusMetrics.systemMetrics.energy) {
          errors.push("Missing Oculus energy metrics");
        } else {
          if (oculusMetrics.systemMetrics.energy.efficiency < 0.5) {
            warnings.push("Low energy efficiency");
            recommendations.push("Improve energy efficiency");
          }
          if (oculusMetrics.systemMetrics.energy.thermalState > 0.8) {
            warnings.push("High thermal state");
            recommendations.push("Improve thermal management");
          }
        }
      }
      
      // Validate meta-awareness
      if (!oculusMetrics.metaAwareness) {
        errors.push("Missing Oculus meta-awareness metrics");
      } else {
        if (oculusMetrics.metaAwareness.coherenceScore < this.config.minCoherenceScore) {
          warnings.push("Low meta-awareness coherence score");
          recommendations.push("Improve meta-awareness coherence");
        }
        if (oculusMetrics.metaAwareness.adaptiveSamplingRate < 0.1) {
          warnings.push("Very low adaptive sampling rate");
          recommendations.push("Increase adaptive sampling rate");
        }
      }
      
      // Validate performance
      if (!oculusMetrics.performance) {
        errors.push("Missing Oculus performance metrics");
      } else {
        if (oculusMetrics.performance.overheadPercent > 0.1) { // 10%
          warnings.push("High Oculus overhead");
          recommendations.push("Reduce Oculus overhead");
        }
      }
      
      // Validate holographic correspondence
      if (!oculusMetrics.holographicCorrespondence || oculusMetrics.holographicCorrespondence.length === 0) {
        errors.push("Missing Oculus holographic correspondence");
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (oculusMetrics.systemMetrics?.compute?.efficiency || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Oculus validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix Oculus validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate coherence analysis
   */
  private async validateCoherenceAnalysis(coherenceAnalysis: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate overall score
      if (typeof coherenceAnalysis.overallScore !== 'number' || coherenceAnalysis.overallScore < 0 || coherenceAnalysis.overallScore > 1) {
        errors.push("Invalid coherence overall score");
      } else if (coherenceAnalysis.overallScore < this.config.minCoherenceScore) {
        errors.push("Coherence score below threshold");
        recommendations.push("Improve coherence through optimization");
      }
      
      // Validate breakdown
      if (!coherenceAnalysis.breakdown) {
        errors.push("Missing coherence breakdown");
      } else {
        const breakdownFields = ['holographicCorrespondence', 'mathematicalConsistency', 'physicalConservation', 'logicalCoherence', 'temporalConsistency'];
        for (const field of breakdownFields) {
          if (typeof coherenceAnalysis.breakdown[field] !== 'number' || coherenceAnalysis.breakdown[field] < 0 || coherenceAnalysis.breakdown[field] > 1) {
            errors.push(`Invalid coherence breakdown for ${field}`);
          } else if (coherenceAnalysis.breakdown[field] < 0.5) {
            warnings.push(`Low coherence score for ${field}`);
            recommendations.push(`Improve ${field} coherence`);
          }
        }
      }
      
      // Validate validation
      if (!coherenceAnalysis.validation) {
        errors.push("Missing coherence validation");
      } else {
        if (!coherenceAnalysis.validation.isCoherent) {
          errors.push("Coherence validation failed");
        }
        if (coherenceAnalysis.validation.confidence < this.config.minCoherenceScore) {
          warnings.push("Low coherence validation confidence");
          recommendations.push("Improve coherence validation");
        }
        if (coherenceAnalysis.validation.violations && coherenceAnalysis.validation.violations.length > 0) {
          errors.push(`Coherence violations: ${coherenceAnalysis.validation.violations.join(', ')}`);
        }
      }
      
      // Validate metrics
      if (!coherenceAnalysis.metrics) {
        errors.push("Missing coherence metrics");
      } else {
        if (coherenceAnalysis.metrics.totalTimeMs > this.config.maxComponentValidationTimeMs) {
          warnings.push("Coherence analysis took too long");
          recommendations.push("Optimize coherence analysis performance");
        }
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (coherenceAnalysis.overallScore || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Coherence validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix coherence validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate performance metrics
   */
  private async validatePerformanceMetrics(performanceMetrics: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate timing
      if (!performanceMetrics.timing) {
        errors.push("Missing performance timing metrics");
      } else {
        if (performanceMetrics.timing.executionTimeMs < 0) {
          errors.push("Invalid execution time");
        }
        if (performanceMetrics.timing.totalTimeMs > 30000) { // 30 seconds
          warnings.push("Very long execution time");
          recommendations.push("Optimize execution performance");
        }
        if (performanceMetrics.timing.overheadTimeMs > performanceMetrics.timing.executionTimeMs * 0.5) {
          warnings.push("High overhead ratio");
          recommendations.push("Reduce system overhead");
        }
      }
      
      // Validate resources
      if (!performanceMetrics.resources) {
        errors.push("Missing performance resource metrics");
      } else {
        if (performanceMetrics.resources.memoryBytes > 1000000000) { // 1GB
          warnings.push("High memory usage");
          recommendations.push("Optimize memory usage");
        }
        if (performanceMetrics.resources.energyJoules > 1000) { // 1kJ
          warnings.push("High energy consumption");
          recommendations.push("Optimize energy usage");
        }
      }
      
      // Validate characteristics
      if (!performanceMetrics.characteristics) {
        errors.push("Missing performance characteristics");
      } else {
        if (performanceMetrics.characteristics.efficiency < this.config.minPerformanceScore) {
          warnings.push("Low performance efficiency");
          recommendations.push("Improve performance efficiency");
        }
        if (performanceMetrics.characteristics.latency > 1000) { // 1 second
          warnings.push("High latency");
          recommendations.push("Optimize latency");
        }
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (performanceMetrics.characteristics?.efficiency || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Performance validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix performance validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate compute metrics
   */
  private async validateComputeMetrics(computeMetrics: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate complexity
      if (!computeMetrics.complexity) {
        errors.push("Missing compute complexity metrics");
      } else {
        if (!computeMetrics.complexity.timeComplexity || typeof computeMetrics.complexity.timeComplexity !== 'string') {
          errors.push("Invalid time complexity");
        }
        if (!computeMetrics.complexity.spaceComplexity || typeof computeMetrics.complexity.spaceComplexity !== 'string') {
          errors.push("Invalid space complexity");
        }
        if (computeMetrics.complexity.actualComplexity < 0) {
          errors.push("Invalid actual complexity");
        }
        if (computeMetrics.complexity.theoreticalComplexity < 0) {
          errors.push("Invalid theoretical complexity");
        }
      }
      
      // Validate efficiency
      if (!computeMetrics.efficiency) {
        errors.push("Missing compute efficiency metrics");
      } else {
        if (computeMetrics.efficiency.overallEfficiency < this.config.minComputeEfficiency) {
          warnings.push("Low overall compute efficiency");
          recommendations.push("Improve compute efficiency");
        }
        if (computeMetrics.efficiency.cpuEfficiency < 0.5) {
          warnings.push("Low CPU efficiency");
          recommendations.push("Optimize CPU usage");
        }
        if (computeMetrics.efficiency.memoryEfficiency < 0.5) {
          warnings.push("Low memory efficiency");
          recommendations.push("Optimize memory usage");
        }
        if (computeMetrics.efficiency.energyEfficiency < 0.5) {
          warnings.push("Low energy efficiency");
          recommendations.push("Optimize energy usage");
        }
      }
      
      // Validate characteristics
      if (!computeMetrics.characteristics) {
        errors.push("Missing compute characteristics");
      }
      
      // Validate FLOPS
      if (!computeMetrics.flops) {
        errors.push("Missing FLOPS metrics");
      } else {
        if (computeMetrics.flops.total < 0) {
          errors.push("Invalid total FLOPS");
        }
        if (computeMetrics.flops.total > 1000000000000) { // 1 trillion
          warnings.push("Very high FLOPS count");
          recommendations.push("Consider optimization for high-compute operations");
        }
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (computeMetrics.efficiency?.overallEfficiency || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Compute validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix compute validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate provenance chain
   */
  private async validateProvenanceChain(provenanceChain: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate chain ID
      if (!provenanceChain.chainId || provenanceChain.chainId.length === 0) {
        errors.push("Missing provenance chain ID");
      }
      
      // Validate chain structure
      if (provenanceChain.totalEntries < 0) {
        errors.push("Invalid total entries count");
      }
      if (provenanceChain.maxDepth < 0) {
        errors.push("Invalid max depth");
      }
      
      // Validate integrity
      if (!provenanceChain.integrity) {
        errors.push("Missing provenance integrity");
      } else {
        if (!provenanceChain.integrity.isComplete) {
          errors.push("Provenance chain is incomplete");
        }
        if (!provenanceChain.integrity.isConsistent) {
          errors.push("Provenance chain is inconsistent");
        }
        if (!provenanceChain.integrity.isVerifiable) {
          errors.push("Provenance chain is not verifiable");
        }
        if (provenanceChain.integrity.missingEntries && provenanceChain.integrity.missingEntries.length > 0) {
          errors.push(`Missing provenance entries: ${provenanceChain.integrity.missingEntries.join(', ')}`);
        }
        if (provenanceChain.integrity.inconsistentEntries && provenanceChain.integrity.inconsistentEntries.length > 0) {
          errors.push(`Inconsistent provenance entries: ${provenanceChain.integrity.inconsistentEntries.join(', ')}`);
        }
      }
      
      // Validate metadata
      if (!provenanceChain.metadata) {
        errors.push("Missing provenance metadata");
      } else {
        if (provenanceChain.metadata.totalOperations < 0) {
          errors.push("Invalid total operations count");
        }
        if (provenanceChain.metadata.totalComplexity < 0) {
          errors.push("Invalid total complexity");
        }
        if (provenanceChain.metadata.averageConfidence < 0 || provenanceChain.metadata.averageConfidence > 1) {
          errors.push("Invalid average confidence");
        }
      }
      
      // Validate holographic correspondence
      if (!provenanceChain.holographicCorrespondence || provenanceChain.holographicCorrespondence.length === 0) {
        errors.push("Missing provenance holographic correspondence");
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (provenanceChain.metadata?.averageConfidence || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Provenance validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix provenance validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate witness verification
   */
  private async validateWitnessVerification(witnessVerification: any): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate signature
      if (!witnessVerification.signature || witnessVerification.signature.length === 0) {
        errors.push("Missing witness signature");
      }
      
      // Validate verification
      if (!witnessVerification.verification) {
        errors.push("Missing witness verification");
      } else {
        if (!witnessVerification.verification.isValid) {
          errors.push("Witness signature verification failed");
        }
        if (witnessVerification.verification.confidence < this.config.minWitnessConfidence) {
          errors.push("Witness signature confidence below threshold");
          recommendations.push("Improve witness signature generation");
        }
        if (witnessVerification.verification.verificationTimeMs > this.config.maxComponentValidationTimeMs) {
          warnings.push("Witness verification took too long");
          recommendations.push("Optimize witness verification performance");
        }
      }
      
      // Validate metadata
      if (!witnessVerification.metadata) {
        errors.push("Missing witness metadata");
      } else {
        if (!witnessVerification.metadata.algorithm || witnessVerification.metadata.algorithm.length === 0) {
          errors.push("Missing witness algorithm");
        }
        if (!witnessVerification.metadata.keyId || witnessVerification.metadata.keyId.length === 0) {
          errors.push("Missing witness key ID");
        }
        if (!witnessVerification.metadata.timestamp || witnessVerification.metadata.timestamp.length === 0) {
          errors.push("Missing witness timestamp");
        }
      }
      
      // Validate integrity
      if (!witnessVerification.integrity) {
        errors.push("Missing witness integrity");
      } else {
        if (witnessVerification.integrity.isTampered) {
          errors.push("Witness signature has been tampered with");
        }
        if (witnessVerification.integrity.isExpired) {
          warnings.push("Witness signature has expired");
          recommendations.push("Regenerate witness signature");
        }
        if (witnessVerification.integrity.isRevoked) {
          errors.push("Witness signature has been revoked");
        }
        if (!witnessVerification.integrity.checksum || witnessVerification.integrity.checksum.length === 0) {
          errors.push("Missing witness checksum");
        }
      }
      
      const isValid = errors.length === 0;
      const confidence = isValid ? (witnessVerification.verification?.confidence || 0) : 0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Witness validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix witness validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Validate holographic correspondence
   */
  private async validateHolographicCorrespondence(metadataReport: StandardizedMetadataReport): Promise<ComponentValidationResult> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    const recommendations: string[] = [];
    
    try {
      // Validate holographic correspondence
      if (!metadataReport.holographicCorrespondence || metadataReport.holographicCorrespondence.length === 0) {
        errors.push("Missing holographic correspondence");
      } else {
        // Verify holographic correspondence integrity
        const expectedCorrespondence = ccmHash({
          proofId: metadataReport.proofId,
          oracle: metadataReport.oracle.holographicCorrespondence,
          oculus: metadataReport.oculus.holographicCorrespondence,
          coherence: metadataReport.coherence.overallScore,
          performance: metadataReport.performance.timing.totalTimeMs,
          compute: metadataReport.compute.complexity.actualComplexity,
          provenance: metadataReport.provenance.chainId,
          witness: metadataReport.witness.signature,
          timestamp: metadataReport.timestamp
        }, "standardized_metadata_report");
        
        if (metadataReport.holographicCorrespondence !== expectedCorrespondence) {
          errors.push("Holographic correspondence mismatch");
          recommendations.push("Regenerate holographic correspondence");
        }
      }
      
      // Validate individual component holographic correspondences
      if (!metadataReport.oracle.holographicCorrespondence || metadataReport.oracle.holographicCorrespondence.length === 0) {
        errors.push("Missing Oracle holographic correspondence");
      }
      if (!metadataReport.oculus.holographicCorrespondence || metadataReport.oculus.holographicCorrespondence.length === 0) {
        errors.push("Missing Oculus holographic correspondence");
      }
      // Note: holographicCorrespondence is validated in the provenance chain validation, not here
      
      const isValid = errors.length === 0;
      const confidence = isValid ? 1.0 : 0.0;
      const score = this.calculateComponentScore(errors, warnings, confidence);
      
      return {
        isValid,
        confidence,
        score,
        errors,
        warnings,
        recommendations,
        validationTimeMs: Date.now() - startTime
      };
      
    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        score: 0,
        errors: [`Holographic validation error: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        recommendations: ["Fix holographic validation implementation"],
        validationTimeMs: Date.now() - startTime
      };
    }
  }
  
  /**
   * Calculate overall validation status
   */
  private calculateOverallValidation(components: any): {
    isValid: boolean;
    confidence: number;
    status: 'valid' | 'invalid' | 'warning' | 'error';
  } {
    const componentResults = Object.values(components) as ComponentValidationResult[];
    const validComponents = componentResults.filter(result => result.isValid).length;
    const totalComponents = componentResults.length;
    const confidence = componentResults.reduce((sum, result) => sum + result.confidence, 0) / totalComponents;
    
    const hasErrors = componentResults.some(result => result.errors.length > 0);
    const hasWarnings = componentResults.some(result => result.warnings.length > 0);
    
    let status: 'valid' | 'invalid' | 'warning' | 'error';
    if (hasErrors) {
      status = 'error';
    } else if (hasWarnings) {
      status = 'warning';
    } else {
      status = 'valid';
    }
    
    const isValid = validComponents === totalComponents && !hasErrors;
    
    return { isValid, confidence, status };
  }
  
  /**
   * Collect validation details
   */
  private collectValidationDetails(components: any): {
    errors: ValidationError[];
    warnings: ValidationWarning[];
    recommendations: ValidationRecommendation[];
  } {
    const errors: ValidationError[] = [];
    const warnings: ValidationWarning[] = [];
    const recommendations: ValidationRecommendation[] = [];
    
    for (const [componentName, componentResult] of Object.entries(components)) {
      const result = componentResult as ComponentValidationResult;
      
      // Collect errors
      for (const error of result.errors) {
        errors.push({
          component: componentName,
          field: 'general',
          code: 'VALIDATION_ERROR',
          message: error,
          severity: 'high',
          timestamp: new Date().toISOString()
        });
      }
      
      // Collect warnings
      for (const warning of result.warnings) {
        warnings.push({
          component: componentName,
          field: 'general',
          code: 'VALIDATION_WARNING',
          message: warning,
          impact: 'performance',
          timestamp: new Date().toISOString()
        });
      }
      
      // Collect recommendations
      for (const recommendation of result.recommendations) {
        recommendations.push({
          component: componentName,
          field: 'general',
          code: 'VALIDATION_RECOMMENDATION',
          message: recommendation,
          priority: 'medium',
          action: 'optimize',
          timestamp: new Date().toISOString()
        });
      }
    }
    
    return { errors, warnings, recommendations };
  }
  
  /**
   * Calculate component score
   */
  private calculateComponentScore(errors: string[], warnings: string[], confidence: number): number {
    let score = confidence;
    
    // Penalize errors
    score -= errors.length * 0.2;
    
    // Penalize warnings
    score -= warnings.length * 0.1;
    
    return Math.max(0, Math.min(1, score));
  }
  
  /**
   * Generate validation ID
   */
  private generateValidationId(): string {
    return ccmHash({ timestamp: Date.now(), random: Math.random() }, "validation_id");
  }
}

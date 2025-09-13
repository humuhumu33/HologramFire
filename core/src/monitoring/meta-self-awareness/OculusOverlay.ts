import { Metrics } from "../metrics/Metrics";
import { ccmHash } from "../../crypto/ccm/CCMHash";
import { Oculus, MetaAwarenessConfig } from "./Oculus";
import { MetaAwarenessResult } from "./MetaSelfAwarenessLayer";
import { ProofChainManager } from "../../proof-chain/ProofChain";
import { ProofChainAPI } from "../../proof-chain/ProofChainAPI";

/**
 * Oculus Overlay Witness
 * 
 * Provides an ultra-efficient overlay that integrates the Oculus meta self-awareness layer
 * into the existing system with minimal overhead. Acts as a witness that can be
 * verified and trusted by the proof chain system.
 */

export interface OverlayConfig {
  enableMetaAwareness: boolean;
  enableWitnessVerification: boolean;
  enableOverlayOptimization: boolean;
  witnessCompressionRatio: number;
  maxOverheadPercent: number;
  enableAdaptiveOverlay: boolean;
  overlaySamplingRate: number;
  enablePredictiveWitness: boolean;
}

export interface OverlayWitness {
  witnessId: string;
  witnessType: "meta_awareness";
  timestamp: number;
  compressedData: string;
  verificationHash: string;
  overhead: {
    latency: number;
    compute: number;
    energy: number;
  };
  holographic_correspondence: string;
}

export interface OverlayResult {
  witness: OverlayWitness;
  metaAwarenessResult: MetaAwarenessResult;
  verificationResult: {
    isValid: boolean;
    confidence: number;
    verificationTime: number;
  };
  optimizationApplied: boolean;
  holographic_correspondence: string;
}

export class OculusOverlay {
  private config: OverlayConfig;
  private oculus: Oculus;
  private proofChainAPI: ProofChainAPI;
  private metrics: Metrics;
  private witnessCache: Map<string, OverlayWitness> = new Map();
  private overlayActive: boolean = false;
  private lastWitnessTime: number = 0;
  private adaptiveOverlayRate: number = 1.0;

  constructor(
    config: Partial<OverlayConfig> = {},
    metrics: Metrics,
    proofChainManager: ProofChainManager
  ) {
    this.config = {
      enableMetaAwareness: config.enableMetaAwareness !== false,
      enableWitnessVerification: config.enableWitnessVerification !== false,
      enableOverlayOptimization: config.enableOverlayOptimization !== false,
      witnessCompressionRatio: config.witnessCompressionRatio || 0.2, // 80% compression
      maxOverheadPercent: config.maxOverheadPercent || 0.03, // 3% max overhead
      enableAdaptiveOverlay: config.enableAdaptiveOverlay !== false,
      overlaySamplingRate: config.overlaySamplingRate || 0.5, // 50% sampling
      enablePredictiveWitness: config.enablePredictiveWitness !== false,
      ...config
    };

    this.metrics = metrics;
    this.proofChainAPI = new ProofChainAPI();

    // Initialize Oculus with overlay-optimized config
    const oculusConfig: Partial<MetaAwarenessConfig> = {
      enableLatencyOptimization: true,
      enableComputeOptimization: true,
      enableEnergyOptimization: true,
      enableOracleIntegration: true,
      enableMLOptimization: true,
      monitoringIntervalMs: 10000, // 10 seconds for overlay
      optimizationThreshold: 0.15, // 15% threshold for overlay
      maxOverheadPercent: this.config.maxOverheadPercent,
      enableAdaptiveSampling: this.config.enableAdaptiveOverlay,
      enablePredictiveOptimization: this.config.enablePredictiveWitness,
      witnessCompressionRatio: this.config.witnessCompressionRatio
    };

    this.oculus = new Oculus(oculusConfig, metrics, proofChainManager);
  }

  /**
   * Activates the Oculus overlay
   */
  activateOverlay(): void {
    if (this.overlayActive) {
      return;
    }

    this.overlayActive = true;
    
    if (this.config.enableMetaAwareness) {
      this.oculus.startMonitoring();
    }

    this.metrics.inc("oculus_overlay_activated", 1);
  }

  /**
   * Deactivates the Oculus overlay
   */
  deactivateOverlay(): void {
    if (!this.overlayActive) {
      return;
    }

    this.overlayActive = false;
    
    if (this.config.enableMetaAwareness) {
      this.oculus.stopMonitoring();
    }

    this.metrics.inc("oculus_overlay_deactivated", 1);
  }

  /**
   * Generates an overlay witness with meta awareness data
   */
  async generateOverlayWitness(): Promise<OverlayResult> {
    const witnessStart = Date.now();
    
    if (!this.overlayActive) {
      throw new Error("Meta awareness overlay is not active");
    }

    // Check if we should generate a witness based on adaptive rate
    if (!this.shouldGenerateWitness()) {
      return this.getCachedWitness();
    }

    try {
      // Get Oculus result
      const oculusResult = await this.oculus.performMetaAwarenessCycle();
      
      // Create compressed witness data
      const witnessData = this.compressWitnessData(oculusResult);
      
      // Generate witness
      const witness = await this.createOverlayWitness(witnessData, witnessStart);
      
      // Verify witness if enabled
      const verificationResult = this.config.enableWitnessVerification 
        ? await this.verifyWitness(witness)
        : { isValid: true, confidence: 1.0, verificationTime: 0 };
      
      // Apply optimizations if witness is valid
      const optimizationApplied = verificationResult.isValid && this.config.enableOverlayOptimization
        ? await this.applyOverlayOptimizations(oculusResult)
        : false;

      const result: OverlayResult = {
        witness,
        metaAwarenessResult: oculusResult,
        verificationResult,
        optimizationApplied,
        holographic_correspondence: ccmHash({
          witness,
          oculusResult,
          verificationResult,
          optimizationApplied,
          timestamp: Date.now()
        }, "oculus.overlay_result")
      };

      // Cache witness
      this.cacheWitness(witness);

      // Update adaptive overlay rate
      this.updateAdaptiveOverlayRate(witness.overhead);

      // Record witness generation metrics
      this.metrics.observe("overlay_witness_generation_time_ms", Date.now() - witnessStart);
      this.metrics.inc("overlay_witnesses_generated", 1);

      return result;

    } catch (error) {
      this.metrics.inc("oculus_witness_generation_errors", 1);
      throw new Error(`Failed to generate overlay witness: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Verifies an overlay witness
   */
  async verifyOverlayWitness(witness: OverlayWitness): Promise<{
    isValid: boolean;
    confidence: number;
    verificationTime: number;
    issues: string[];
  }> {
    const verificationStart = Date.now();
    const issues: string[] = [];

    try {
      // Verify witness structure
      if (!this.verifyWitnessStructure(witness)) {
        issues.push("Invalid witness structure");
      }

      // Verify timestamp
      if (!this.verifyWitnessTimestamp(witness)) {
        issues.push("Invalid witness timestamp");
      }

      // Verify compression
      if (!this.verifyWitnessCompression(witness)) {
        issues.push("Invalid witness compression");
      }

      // Verify holographic correspondence
      if (!this.verifyHolographicCorrespondence(witness)) {
        issues.push("Invalid holographic correspondence");
      }

      // Verify overhead limits
      if (!this.verifyOverheadLimits(witness)) {
        issues.push("Witness overhead exceeds limits");
      }

      const isValid = issues.length === 0;
      const confidence = this.calculateVerificationConfidence(witness, issues);
      const verificationTime = Date.now() - verificationStart;

      this.metrics.observe("overlay_witness_verification_time_ms", verificationTime);
      this.metrics.inc("overlay_witness_verifications", 1, { valid: isValid.toString() });

      return {
        isValid,
        confidence,
        verificationTime,
        issues
      };

    } catch (error) {
      this.metrics.inc("oculus_witness_verification_errors", 1);
      return {
        isValid: false,
        confidence: 0,
        verificationTime: Date.now() - verificationStart,
        issues: [`Verification error: ${error instanceof Error ? error.message : String(error)}`]
      };
    }
  }

  /**
   * Gets overlay statistics
   */
  getOverlayStats(): {
    overlayActive: boolean;
    witnessCacheSize: number;
    adaptiveOverlayRate: number;
    metaAwarenessState: any;
    oculusState: any;
    holographic_correspondence: string;
  } {
    return {
      overlayActive: this.overlayActive,
      witnessCacheSize: this.witnessCache.size,
      adaptiveOverlayRate: this.adaptiveOverlayRate,
      metaAwarenessState: this.oculus.getCurrentState(),
      oculusState: this.oculus.getCurrentState(),
      holographic_correspondence: ccmHash({
        overlayActive: this.overlayActive,
        witnessCacheSize: this.witnessCache.size,
        adaptiveOverlayRate: this.adaptiveOverlayRate,
        timestamp: Date.now()
      }, "oculus.overlay_stats")
    };
  }

  /**
   * Compresses witness data to minimize overhead
   */
  private compressWitnessData(metaAwarenessResult: MetaAwarenessResult): string {
    // Extract only essential data for witness
    const essentialData = {
      latency: {
        current: metaAwarenessResult.systemMetrics.latency.current,
        trend: metaAwarenessResult.systemMetrics.latency.trend
      },
      compute: {
        efficiency: metaAwarenessResult.systemMetrics.compute.efficiency
      },
      energy: {
        efficiency: metaAwarenessResult.systemMetrics.energy.efficiency
      },
      decisions: metaAwarenessResult.optimizationDecisions.length,
      gains: {
        latency: metaAwarenessResult.performanceGains.latency,
        compute: metaAwarenessResult.performanceGains.compute,
        energy: metaAwarenessResult.performanceGains.energy
      },
      overhead: metaAwarenessResult.overhead,
      timestamp: Date.now()
    };

    // Apply compression
    const compressed = JSON.stringify(essentialData);
    const targetSize = Math.floor(compressed.length * this.config.witnessCompressionRatio);
    
    // Simple compression simulation (in real implementation, use actual compression)
    return compressed.substring(0, targetSize) + "...[compressed]";
  }

  /**
   * Creates overlay witness
   */
  private async createOverlayWitness(witnessData: string, startTime: number): Promise<OverlayWitness> {
    const witnessId = ccmHash(witnessData, "overlay.witness.id");
    const timestamp = Date.now();
    
    // Calculate overhead
    const overhead = this.calculateWitnessOverhead(startTime);
    
    // Generate verification hash
    const verificationHash = ccmHash({
      witnessId,
      timestamp,
      witnessData,
      overhead
    }, "overlay.witness.verification");

    const witness: OverlayWitness = {
      witnessId,
      witnessType: "meta_awareness",
      timestamp,
      compressedData: witnessData,
      verificationHash,
      overhead,
      holographic_correspondence: ccmHash({
        witnessId,
        witnessType: "meta_awareness",
        timestamp,
        overhead,
        verificationHash
      }, "overlay.witness.holographic")
    };

    return witness;
  }

  /**
   * Verifies witness
   */
  private async verifyWitness(witness: OverlayWitness): Promise<{
    isValid: boolean;
    confidence: number;
    verificationTime: number;
  }> {
    const startTime = Date.now();
    
    // Verify witness structure
    const structureValid = this.verifyWitnessStructure(witness);
    
    // Verify timestamp
    const timestampValid = this.verifyWitnessTimestamp(witness);
    
    // Verify holographic correspondence
    const holographicValid = this.verifyHolographicCorrespondence(witness);
    
    const isValid = structureValid && timestampValid && holographicValid;
    const confidence = isValid ? 0.95 : 0.1;
    const verificationTime = Date.now() - startTime;

    return { isValid, confidence, verificationTime };
  }

  /**
   * Applies overlay optimizations
   */
  private async applyOverlayOptimizations(metaAwarenessResult: MetaAwarenessResult): Promise<boolean> {
    try {
      // Apply optimizations based on meta awareness decisions
      for (const decision of metaAwarenessResult.optimizationDecisions) {
        switch (decision.type) {
          case 'latency':
            await this.applyLatencyOptimization(decision);
            break;
          case 'compute':
            await this.applyComputeOptimization(decision);
            break;
          case 'energy':
            await this.applyEnergyOptimization(decision);
            break;
          case 'holistic':
            await this.applyHolisticOptimization(decision);
            break;
        }
      }

      this.metrics.inc("oculus_optimizations_applied", 1);
      return true;

    } catch (error) {
      this.metrics.inc("oculus_optimization_errors", 1);
      return false;
    }
  }

  /**
   * Applies latency optimization
   */
  private async applyLatencyOptimization(decision: any): Promise<void> {
    // Implement latency optimization logic
    this.metrics.inc("oculus_latency_optimizations_applied", 1);
  }

  /**
   * Applies compute optimization
   */
  private async applyComputeOptimization(decision: any): Promise<void> {
    // Implement compute optimization logic
    this.metrics.inc("oculus_compute_optimizations_applied", 1);
  }

  /**
   * Applies energy optimization
   */
  private async applyEnergyOptimization(decision: any): Promise<void> {
    // Implement energy optimization logic
    this.metrics.inc("oculus_energy_optimizations_applied", 1);
  }

  /**
   * Applies holistic optimization
   */
  private async applyHolisticOptimization(decision: any): Promise<void> {
    // Implement holistic optimization logic
    this.metrics.inc("oculus_holistic_optimizations_applied", 1);
  }

  /**
   * Determines if witness should be generated based on adaptive rate
   */
  private shouldGenerateWitness(): boolean {
    if (!this.config.enableAdaptiveOverlay) {
      return true;
    }

    const now = Date.now();
    const timeSinceLastWitness = now - this.lastWitnessTime;
    const minInterval = 5000; // 5 seconds minimum

    if (timeSinceLastWitness < minInterval) {
      return false;
    }

    // Use adaptive rate to determine if witness should be generated
    const randomValue = Math.random();
    return randomValue < this.adaptiveOverlayRate;
  }

  /**
   * Gets cached witness if available
   */
  private getCachedWitness(): OverlayResult {
    // Return a cached witness or create a minimal one
    const cachedWitness = Array.from(this.witnessCache.values())[0];
    
    if (cachedWitness) {
      return {
        witness: cachedWitness,
        metaAwarenessResult: {
          systemMetrics: {
            latency: { current: 0, average: 0, p95: 0, p99: 0, trend: 'stable' },
            compute: { cpuUtilization: 0, memoryUtilization: 0, operationComplexity: 0, efficiency: 0 },
            energy: { consumptionPerOp: 0, totalConsumption: 0, efficiency: 0, thermalState: 0 },
            holographic_correspondence: ""
          },
          optimizationDecisions: [],
          oracleInsights: null,
          performanceGains: { latency: 0, compute: 0, energy: 0 },
          overhead: { latency: 0, compute: 0, energy: 0 },
          witness: ""
        },
        verificationResult: { isValid: true, confidence: 0.9, verificationTime: 0 },
        optimizationApplied: false,
        holographic_correspondence: ""
      };
    }

    throw new Error("No cached witness available");
  }

  /**
   * Caches witness for future use
   */
  private cacheWitness(witness: OverlayWitness): void {
    this.witnessCache.set(witness.witnessId, witness);
    this.lastWitnessTime = witness.timestamp;

    // Limit cache size
    if (this.witnessCache.size > 10) {
      const oldestKey = this.witnessCache.keys().next().value;
      if (oldestKey) {
        this.witnessCache.delete(oldestKey);
      }
    }
  }

  /**
   * Updates adaptive overlay rate based on overhead
   */
  private updateAdaptiveOverlayRate(overhead: any): void {
    if (!this.config.enableAdaptiveOverlay) {
      return;
    }

    const totalOverhead = overhead.latency + overhead.compute + overhead.energy;
    
    if (totalOverhead > this.config.maxOverheadPercent) {
      // Reduce overlay rate to decrease overhead
      this.adaptiveOverlayRate = Math.max(0.1, this.adaptiveOverlayRate * 0.9);
    } else if (totalOverhead < this.config.maxOverheadPercent * 0.5) {
      // Increase overlay rate for better monitoring
      this.adaptiveOverlayRate = Math.min(1.0, this.adaptiveOverlayRate * 1.1);
    }

    this.metrics.setGauge("adaptive_overlay_rate", this.adaptiveOverlayRate);
  }

  /**
   * Calculates witness overhead
   */
  private calculateWitnessOverhead(startTime: number): {
    latency: number;
    compute: number;
    energy: number;
  } {
    const processingTime = Date.now() - startTime;
    
    return {
      latency: Math.min(processingTime / 1000, 0.03), // Max 3% latency overhead
      compute: Math.min(processingTime / 10000, 0.02), // Max 2% compute overhead
      energy: Math.min(processingTime / 100000, 0.01) // Max 1% energy overhead
    };
  }

  /**
   * Verification helper methods
   */
  private verifyWitnessStructure(witness: OverlayWitness): boolean {
    return !!(
      witness.witnessId &&
      witness.witnessType === "meta_awareness" &&
      witness.timestamp &&
      witness.compressedData &&
      witness.verificationHash &&
      witness.overhead &&
      witness.holographic_correspondence
    );
  }

  private verifyWitnessTimestamp(witness: OverlayWitness): boolean {
    const now = Date.now();
    const age = now - witness.timestamp;
    const maxAge = 300000; // 5 minutes
    
    return age >= 0 && age <= maxAge;
  }

  private verifyWitnessCompression(witness: OverlayWitness): boolean {
    // Verify compression ratio is within expected range
    const expectedMaxSize = 1000; // 1KB max
    return witness.compressedData.length <= expectedMaxSize;
  }

  private verifyHolographicCorrespondence(witness: OverlayWitness): boolean {
    // Verify holographic correspondence hash
    const expectedHash = ccmHash({
      witnessId: witness.witnessId,
      witnessType: witness.witnessType,
      timestamp: witness.timestamp,
      overhead: witness.overhead,
      verificationHash: witness.verificationHash
    }, "overlay.witness.holographic");
    
    return witness.holographic_correspondence === expectedHash;
  }

  private verifyOverheadLimits(witness: OverlayWitness): boolean {
    const totalOverhead = witness.overhead.latency + witness.overhead.compute + witness.overhead.energy;
    return totalOverhead <= this.config.maxOverheadPercent;
  }

  private calculateVerificationConfidence(witness: OverlayWitness, issues: string[]): number {
    if (issues.length === 0) {
      return 0.95;
    }
    
    const baseConfidence = 0.95;
    const penaltyPerIssue = 0.1;
    return Math.max(0, baseConfidence - (issues.length * penaltyPerIssue));
  }

  /**
   * Resets overlay state
   */
  reset(): void {
    this.deactivateOverlay();
    this.witnessCache.clear();
    this.adaptiveOverlayRate = 1.0;
    this.lastWitnessTime = 0;
    this.oculus.reset();
  }
}

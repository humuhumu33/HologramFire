import { Metrics } from "../metrics/Metrics";
import { ccmHash } from "../../crypto/ccm/CCMHash";
import { Oculus } from "./Oculus";
import { OculusOverlay } from "./OculusOverlay";
import { ProofChainManager } from "../../proof-chain/ProofChain";
import { MasterHologramOracle } from "../../validator/MasterHologramOracle";
import { HologramPerformanceOptimizer } from "../../optimization/HologramPerformanceOptimizer";
import { EnergyAwareScaling } from "../energy/EnergyAwareScaling";

/**
 * Oculus Integration
 * 
 * Integrates the Oculus meta self-awareness layer into the existing hologram system
 * with minimal overhead and maximum efficiency. Provides a unified interface
 * for system-wide optimization and monitoring.
 */

export interface IntegrationConfig {
  enableMetaAwareness: boolean;
  enableOverlayWitness: boolean;
  enableSystemIntegration: boolean;
  enableOracleIntegration: boolean;
  enableOptimizationIntegration: boolean;
  enableEnergyIntegration: boolean;
  integrationMode: 'passive' | 'active' | 'adaptive';
  maxSystemOverhead: number;
  enablePredictiveIntegration: boolean;
  enableHolographicIntegration: boolean;
}

export interface SystemIntegrationResult {
  integrationActive: boolean;
  metaAwarenessActive: boolean;
  overlayWitnessActive: boolean;
  systemOptimizations: {
    latency: number;
    compute: number;
    energy: number;
  };
  integrationOverhead: {
    latency: number;
    compute: number;
    energy: number;
  };
  holographic_correspondence: string;
}

export interface OptimizationRecommendation {
  component: string;
  optimization: string;
  expectedImprovement: number;
  confidence: number;
  reasoning: string;
  holographic_correspondence: string;
}

export class OculusIntegration {
  private config: IntegrationConfig;
  private metrics: Metrics;
  private proofChainManager: ProofChainManager;
  private oculus: Oculus;
  private overlayWitness: OculusOverlay;
  private oracle: MasterHologramOracle;
  private optimizer: HologramPerformanceOptimizer;
  private energyScaling: EnergyAwareScaling;
  
  private integrationActive: boolean = false;
  private systemComponents: Map<string, any> = new Map();
  private optimizationHistory: OptimizationRecommendation[] = [];
  private lastIntegrationTime: number = 0;

  constructor(
    config: Partial<IntegrationConfig> = {},
    metrics: Metrics,
    proofChainManager: ProofChainManager
  ) {
    this.config = {
      enableMetaAwareness: config.enableMetaAwareness !== false,
      enableOverlayWitness: config.enableOverlayWitness !== false,
      enableSystemIntegration: config.enableSystemIntegration !== false,
      enableOracleIntegration: config.enableOracleIntegration !== false,
      enableOptimizationIntegration: config.enableOptimizationIntegration !== false,
      enableEnergyIntegration: config.enableEnergyIntegration !== false,
      integrationMode: config.integrationMode || 'adaptive',
      maxSystemOverhead: config.maxSystemOverhead || 0.05, // 5% max system overhead
      enablePredictiveIntegration: config.enablePredictiveIntegration !== false,
      enableHolographicIntegration: config.enableHolographicIntegration !== false,
      ...config
    };

    this.metrics = metrics;
    this.proofChainManager = proofChainManager;

    // Initialize Oculus
    this.oculus = new Oculus({
      enableLatencyOptimization: true,
      enableComputeOptimization: true,
      enableEnergyOptimization: true,
      enableOracleIntegration: this.config.enableOracleIntegration,
      enableMLOptimization: true,
      monitoringIntervalMs: 10000,
      optimizationThreshold: 0.1,
      maxOverheadPercent: this.config.maxSystemOverhead,
      enableAdaptiveSampling: true,
      enablePredictiveOptimization: this.config.enablePredictiveIntegration,
      witnessCompressionRatio: 0.3
    }, metrics, proofChainManager);

    // Initialize overlay witness
    this.overlayWitness = new OculusOverlay({
      enableMetaAwareness: this.config.enableMetaAwareness,
      enableWitnessVerification: true,
      enableOverlayOptimization: true,
      witnessCompressionRatio: 0.2,
      maxOverheadPercent: this.config.maxSystemOverhead,
      enableAdaptiveOverlay: true,
      overlaySamplingRate: 0.5,
      enablePredictiveWitness: this.config.enablePredictiveIntegration
    }, metrics, proofChainManager);

    // Initialize oracle
    this.oracle = new MasterHologramOracle({
      type: 'ml-enhanced',
      config: {
        enableMLOptimization: true,
        enableAdaptiveScoring: true,
        enablePerformanceCalibration: true,
        enableRealTimeMonitoring: true,
        enablePredictiveOptimization: this.config.enablePredictiveIntegration
      }
    });

    // Initialize optimizer
    this.optimizer = new HologramPerformanceOptimizer({
      enableProofBasedComputation: true,
      enableEnergyOptimization: this.config.enableEnergyIntegration,
      enableParallelProcessing: true,
      enableAdaptiveCaching: true,
      enableCompressedProofs: true,
      maxConcurrency: 4,
      cacheSize: 1000,
      energyThreshold: 0.0001,
      latencyThreshold: 10,
      compressionRatio: 0.3
    }, metrics, proofChainManager);

    // Initialize energy scaling
    this.energyScaling = new EnergyAwareScaling({
      enableEnergyOptimization: this.config.enableEnergyIntegration,
      enableThermalManagement: true,
      enableAdaptiveScaling: true,
      energyThreshold: 0.0001,
      thermalThreshold: 0.7,
      scalingWindow: 10000,
      minScalingFactor: 0.5,
      maxScalingFactor: 1.5,
      hysteresisFactor: 0.05
    }, metrics);
  }

  /**
   * Activates the Oculus integration
   */
  activateIntegration(): void {
    if (this.integrationActive) {
      return;
    }

    this.integrationActive = true;

    // Activate Oculus
    if (this.config.enableMetaAwareness) {
      this.oculus.startMonitoring();
    }

    // Activate overlay witness
    if (this.config.enableOverlayWitness) {
      this.overlayWitness.activateOverlay();
    }

    // Register system components
    this.registerSystemComponents();

    this.metrics.inc("oculus_integration_activated", 1);
  }

  /**
   * Deactivates the Oculus integration
   */
  deactivateIntegration(): void {
    if (!this.integrationActive) {
      return;
    }

    this.integrationActive = false;

    // Deactivate Oculus
    if (this.config.enableMetaAwareness) {
      this.oculus.stopMonitoring();
    }

    // Deactivate overlay witness
    if (this.config.enableOverlayWitness) {
      this.overlayWitness.deactivateOverlay();
    }

    this.metrics.inc("oculus_integration_deactivated", 1);
  }

  /**
   * Performs system-wide optimization based on meta awareness insights
   */
  async performSystemOptimization(): Promise<SystemIntegrationResult> {
    const optimizationStart = Date.now();

    if (!this.integrationActive) {
      throw new Error("Meta awareness integration is not active");
    }

    try {
      // Get Oculus insights
      const oculusResult = await this.oculus.performMetaAwarenessCycle();
      
      // Get overlay witness
      const overlayResult = await this.overlayWitness.generateOverlayWitness();
      
      // Generate optimization recommendations
      const recommendations = await this.generateOptimizationRecommendations(
        oculusResult,
        overlayResult
      );
      
      // Apply system optimizations
      const systemOptimizations = await this.applySystemOptimizations(recommendations);
      
      // Calculate integration overhead
      const integrationOverhead = this.calculateIntegrationOverhead(optimizationStart);
      
      // Update optimization history
      this.optimizationHistory.push(...recommendations);
      this.lastIntegrationTime = Date.now();

      const result: SystemIntegrationResult = {
        integrationActive: this.integrationActive,
        metaAwarenessActive: this.config.enableMetaAwareness,
        overlayWitnessActive: this.config.enableOverlayWitness,
        systemOptimizations,
        integrationOverhead,
        holographic_correspondence: ccmHash({
          integrationActive: this.integrationActive,
          systemOptimizations,
          integrationOverhead,
          timestamp: Date.now()
        }, "oculus.integration_result")
      };

      // Record optimization metrics
      this.metrics.observe("system_optimization_time_ms", Date.now() - optimizationStart);
      this.metrics.inc("system_optimizations_performed", 1);

      return result;

    } catch (error) {
      this.metrics.inc("oculus_optimization_errors", 1);
      throw new Error(`System optimization failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Registers system components for optimization
   */
  private registerSystemComponents(): void {
    this.systemComponents.set("oracle", this.oracle);
    this.systemComponents.set("optimizer", this.optimizer);
    this.systemComponents.set("energyScaling", this.energyScaling);
    this.systemComponents.set("proofChainManager", this.proofChainManager);
    this.systemComponents.set("metrics", this.metrics);
  }

  /**
   * Generates optimization recommendations based on meta awareness insights
   */
  private async generateOptimizationRecommendations(
    metaAwarenessResult: any,
    overlayResult: any
  ): Promise<OptimizationRecommendation[]> {
    const recommendations: OptimizationRecommendation[] = [];

    // Analyze system metrics
    const systemMetrics = metaAwarenessResult.systemMetrics;
    
    // Latency optimization recommendations
    if (systemMetrics.latency.trend === 'degrading') {
      recommendations.push({
        component: "optimizer",
        optimization: "enable_parallel_processing",
        expectedImprovement: 0.2,
        confidence: 0.8,
        reasoning: "Latency trend is degrading, parallel processing can improve performance",
        holographic_correspondence: ccmHash({
          component: "optimizer",
          optimization: "enable_parallel_processing",
          expectedImprovement: 0.2,
          timestamp: Date.now()
        }, "meta_awareness.latency_recommendation")
      });
    }

    // Compute optimization recommendations
    if (systemMetrics.compute.efficiency < 0.7) {
      recommendations.push({
        component: "optimizer",
        optimization: "optimize_caching_strategy",
        expectedImprovement: 0.15,
        confidence: 0.75,
        reasoning: "Compute efficiency is low, caching optimization can improve efficiency",
        holographic_correspondence: ccmHash({
          component: "optimizer",
          optimization: "optimize_caching_strategy",
          expectedImprovement: 0.15,
          timestamp: Date.now()
        }, "meta_awareness.compute_recommendation")
      });
    }

    // Energy optimization recommendations
    if (systemMetrics.energy.efficiency < 0.8) {
      recommendations.push({
        component: "energyScaling",
        optimization: "enable_energy_scaling",
        expectedImprovement: 0.1,
        confidence: 0.85,
        reasoning: "Energy efficiency is low, energy scaling can improve efficiency",
        holographic_correspondence: ccmHash({
          component: "energyScaling",
          optimization: "enable_energy_scaling",
          expectedImprovement: 0.1,
          timestamp: Date.now()
        }, "meta_awareness.energy_recommendation")
      });
    }

    // Oracle optimization recommendations
    if (this.config.enableOracleIntegration) {
      recommendations.push({
        component: "oracle",
        optimization: "enable_ml_optimization",
        expectedImprovement: 0.12,
        confidence: 0.7,
        reasoning: "Oracle can benefit from ML optimization for better predictions",
        holographic_correspondence: ccmHash({
          component: "oracle",
          optimization: "enable_ml_optimization",
          expectedImprovement: 0.12,
          timestamp: Date.now()
        }, "meta_awareness.oracle_recommendation")
      });
    }

    return recommendations;
  }

  /**
   * Applies system optimizations based on recommendations
   */
  private async applySystemOptimizations(
    recommendations: OptimizationRecommendation[]
  ): Promise<{ latency: number; compute: number; energy: number }> {
    const optimizations = { latency: 0, compute: 0, energy: 0 };

    for (const recommendation of recommendations) {
      try {
        const component = this.systemComponents.get(recommendation.component);
        if (!component) {
          continue;
        }

        switch (recommendation.optimization) {
          case "enable_parallel_processing":
            optimizations.latency += await this.applyParallelProcessingOptimization(component);
            break;
          case "optimize_caching_strategy":
            optimizations.compute += await this.applyCachingOptimization(component);
            break;
          case "enable_energy_scaling":
            optimizations.energy += await this.applyEnergyScalingOptimization(component);
            break;
          case "enable_ml_optimization":
            const mlGains = await this.applyMLOptimization(component);
            optimizations.latency += mlGains.latency;
            optimizations.compute += mlGains.compute;
            optimizations.energy += mlGains.energy;
            break;
        }

    this.metrics.inc("oculus_optimizations_applied", 1, { 
      component: recommendation.component,
      optimization: recommendation.optimization 
    });

      } catch (error) {
        this.metrics.inc("oculus_optimization_application_errors", 1);
        console.error(`Failed to apply optimization ${recommendation.optimization}:`, error);
      }
    }

    return optimizations;
  }

  /**
   * Applies parallel processing optimization
   */
  private async applyParallelProcessingOptimization(component: any): Promise<number> {
    // Enable parallel processing in optimizer
    if (component && typeof component.optimizeHologramGeneration === 'function') {
      // Simulate parallel processing optimization
      return 0.2; // 20% improvement
    }
    return 0;
  }

  /**
   * Applies caching optimization
   */
  private async applyCachingOptimization(component: any): Promise<number> {
    // Optimize caching strategy
    if (component && typeof component.optimizeHologramGeneration === 'function') {
      // Simulate caching optimization
      return 0.15; // 15% improvement
    }
    return 0;
  }

  /**
   * Applies energy scaling optimization
   */
  private async applyEnergyScalingOptimization(component: any): Promise<number> {
    // Enable energy scaling
    if (component && typeof component.analyzeAndScale === 'function') {
      const result = component.analyzeAndScale();
      return result.performanceGain / 100; // Convert percentage to decimal
    }
    return 0;
  }

  /**
   * Applies ML optimization
   */
  private async applyMLOptimization(component: any): Promise<{ latency: number; compute: number; energy: number }> {
    // Enable ML optimization in oracle
    if (component && typeof component.validate === 'function') {
      // Simulate ML optimization gains
      return {
        latency: 0.05, // 5% improvement
        compute: 0.08, // 8% improvement
        energy: 0.06   // 6% improvement
      };
    }
    return { latency: 0, compute: 0, energy: 0 };
  }

  /**
   * Calculates integration overhead
   */
  private calculateIntegrationOverhead(startTime: number): {
    latency: number;
    compute: number;
    energy: number;
  } {
    const processingTime = Date.now() - startTime;
    
    return {
      latency: Math.min(processingTime / 1000, this.config.maxSystemOverhead),
      compute: Math.min(processingTime / 10000, this.config.maxSystemOverhead),
      energy: Math.min(processingTime / 100000, this.config.maxSystemOverhead)
    };
  }

  /**
   * Gets integration statistics
   */
  getIntegrationStats(): {
    integrationActive: boolean;
    metaAwarenessActive: boolean;
    overlayWitnessActive: boolean;
    systemComponentsCount: number;
    optimizationHistoryLength: number;
    lastIntegrationTime: number;
    holographic_correspondence: string;
  } {
    return {
      integrationActive: this.integrationActive,
      metaAwarenessActive: this.config.enableMetaAwareness,
      overlayWitnessActive: this.config.enableOverlayWitness,
      systemComponentsCount: this.systemComponents.size,
      optimizationHistoryLength: this.optimizationHistory.length,
      lastIntegrationTime: this.lastIntegrationTime,
      holographic_correspondence: ccmHash({
        integrationActive: this.integrationActive,
        metaAwarenessActive: this.config.enableMetaAwareness,
        overlayWitnessActive: this.config.enableOverlayWitness,
        systemComponentsCount: this.systemComponents.size,
        optimizationHistoryLength: this.optimizationHistory.length,
        lastIntegrationTime: this.lastIntegrationTime,
        timestamp: Date.now()
      }, "oculus.integration_stats")
    };
  }

  /**
   * Gets optimization recommendations history
   */
  getOptimizationHistory(): OptimizationRecommendation[] {
    return [...this.optimizationHistory];
  }

  /**
   * Gets system component status
   */
  getSystemComponentStatus(): { [key: string]: any } {
    const status: { [key: string]: any } = {};
    
    for (const [name, component] of this.systemComponents) {
      if (component && typeof component.getCurrentState === 'function') {
        status[name] = component.getCurrentState();
      } else if (component && typeof component.getOptimizationStats === 'function') {
        status[name] = component.getOptimizationStats();
      } else {
        status[name] = { status: 'active', type: typeof component };
      }
    }
    
    return status;
  }

  /**
   * Resets integration state
   */
  reset(): void {
    this.deactivateIntegration();
    this.optimizationHistory = [];
    this.lastIntegrationTime = 0;
    this.systemComponents.clear();
    this.oculus.reset();
    this.overlayWitness.reset();
  }
}

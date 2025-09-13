import { Metrics } from "../monitoring/metrics/Metrics";
import { ccmHash } from "../crypto/ccm/CCMHash";
import { stableStringify } from "../crypto/util/stable";
import { ProofChainManager } from "../proof-chain/ProofChain";
import { HologramPerformanceOptimizer, OptimizationResult } from "./HologramPerformanceOptimizer";
import { CompressedProofSystem, ProofOptimizationResult } from "./CompressedProofSystem";
import { EnergyAwareScaling } from "../monitoring/energy/EnergyAwareScaling";

/**
 * Integrated Hologram Optimizer
 * 
 * Combines all optimization strategies to provide comprehensive performance
 * optimization for hologram systems with minimal latency, compute, and energy requirements.
 */

export interface IntegratedOptimizationConfig {
  enableProofBasedComputation: boolean;
  enableCompressedProofs: boolean;
  enableEnergyOptimization: boolean;
  enableParallelProcessing: boolean;
  enableAdaptiveCaching: boolean;
  enableMLOptimization: boolean;
  enableHolographicCompression: boolean;
  optimizationStrategy: "balanced" | "latency" | "energy" | "compute" | "holographic";
  maxConcurrency: number;
  energyThreshold: number;
  latencyThreshold: number;
  compressionRatio: number;
}

export interface IntegratedOptimizationResult {
  operation: string;
  strategy: string;
  performanceGains: {
    latency: number;
    energy: number;
    compute: number;
    compression: number;
  };
  proofOptimization: ProofOptimizationResult | null;
  performanceOptimization: OptimizationResult | null;
  energyScaling: any;
  holographic_correspondence: string;
  totalImprovement: number;
  optimizationTime: number;
}

export interface OptimizationStrategy {
  name: string;
  priority: number;
  weight: {
    latency: number;
    energy: number;
    compute: number;
    compression: number;
  };
  conditions: {
    minInputSize?: number;
    maxLatency?: number;
    maxEnergy?: number;
    requiredInvariants?: string[];
  };
}

export class IntegratedHologramOptimizer {
  private config: IntegratedOptimizationConfig;
  private metrics: Metrics;
  private proofChainManager: ProofChainManager;
  private performanceOptimizer: HologramPerformanceOptimizer;
  private compressedProofSystem: CompressedProofSystem;
  private energyScaling: EnergyAwareScaling;
  private optimizationStrategies: Map<string, OptimizationStrategy> = new Map();
  private optimizationHistory: IntegratedOptimizationResult[] = [];

  constructor(
    config: Partial<IntegratedOptimizationConfig> = {},
    metrics: Metrics,
    proofChainManager: ProofChainManager
  ) {
    this.config = {
      enableProofBasedComputation: config.enableProofBasedComputation !== false,
      enableCompressedProofs: config.enableCompressedProofs !== false,
      enableEnergyOptimization: config.enableEnergyOptimization !== false,
      enableParallelProcessing: config.enableParallelProcessing !== false,
      enableAdaptiveCaching: config.enableAdaptiveCaching !== false,
      enableMLOptimization: config.enableMLOptimization !== false,
      enableHolographicCompression: config.enableHolographicCompression !== false,
      optimizationStrategy: config.optimizationStrategy || "balanced",
      maxConcurrency: config.maxConcurrency || 8,
      energyThreshold: config.energyThreshold || 0.0005,
      latencyThreshold: config.latencyThreshold || 100,
      compressionRatio: config.compressionRatio || 0.3
    };

    this.metrics = metrics;
    this.proofChainManager = proofChainManager;
    
    // Initialize optimization components
    this.performanceOptimizer = new HologramPerformanceOptimizer({
      enableProofBasedComputation: this.config.enableProofBasedComputation,
      enableEnergyOptimization: this.config.enableEnergyOptimization,
      enableParallelProcessing: this.config.enableParallelProcessing,
      enableAdaptiveCaching: this.config.enableAdaptiveCaching,
      enableCompressedProofs: this.config.enableCompressedProofs,
      maxConcurrency: this.config.maxConcurrency,
      energyThreshold: this.config.energyThreshold,
      latencyThreshold: this.config.latencyThreshold,
      compressionRatio: this.config.compressionRatio
    }, metrics, proofChainManager);

    this.compressedProofSystem = new CompressedProofSystem({
      enableCompression: this.config.enableCompressedProofs,
      compressionAlgorithm: this.config.enableHolographicCompression ? "holographic" : "gzip",
      compressionLevel: 6,
      enableProofCaching: this.config.enableAdaptiveCaching,
      maxCacheSize: 10000,
      compressionThreshold: 1024
    }, metrics, proofChainManager);

    this.energyScaling = new EnergyAwareScaling({
      enableEnergyOptimization: this.config.enableEnergyOptimization,
      energyThreshold: this.config.energyThreshold
    }, metrics);

    this.initializeOptimizationStrategies();
  }

  /**
   * Optimizes hologram operation with integrated approach
   */
  async optimizeHologramOperation(
    operation: string,
    input: any,
    hologramFn: (input: any) => any,
    options: {
      invariants?: string[];
      parentProofs?: string[];
      optimizationStrategy?: string;
      priority?: "latency" | "energy" | "compute" | "balanced";
    } = {}
  ): Promise<IntegratedOptimizationResult> {
    const startTime = Date.now();
    const strategy = options.optimizationStrategy || this.config.optimizationStrategy;
    const priority = options.priority || "balanced";

    // Analyze input and select optimal strategy
    const selectedStrategy = this.selectOptimalStrategy(input, strategy, priority);
    
    // Apply integrated optimizations
    const results = await this.applyIntegratedOptimizations(
      operation,
      input,
      hologramFn,
      selectedStrategy,
      options
    );

    // Calculate total improvement
    const totalImprovement = this.calculateTotalImprovement(results);

    const result: IntegratedOptimizationResult = {
      operation,
      strategy: selectedStrategy.name,
      performanceGains: {
        latency: results.performanceOptimization?.latencyImprovement || 0,
        energy: results.performanceOptimization?.energyImprovement || 0,
        compute: results.performanceOptimization?.computeImprovement || 0,
        compression: results.proofOptimization?.compressedProof.compressionRatio || 1.0
      },
      proofOptimization: results.proofOptimization,
      performanceOptimization: results.performanceOptimization,
      energyScaling: results.energyScaling,
      holographic_correspondence: ccmHash({
        operation,
        strategy: selectedStrategy.name,
        improvements: results,
        totalImprovement
      }, "integrated.optimization"),
      totalImprovement,
      optimizationTime: Date.now() - startTime
    };

    this.optimizationHistory.push(result);
    this.metrics.observe("integrated_optimization_time", result.optimizationTime);
    this.metrics.observe("integrated_total_improvement", totalImprovement);

    return result;
  }

  /**
   * Selects optimal optimization strategy based on input and requirements
   */
  private selectOptimalStrategy(
    input: any,
    strategy: string,
    priority: string
  ): OptimizationStrategy {
    const inputSize = JSON.stringify(input).length;
    const availableStrategies = Array.from(this.optimizationStrategies.values());

    // Filter strategies based on conditions
    const applicableStrategies = availableStrategies.filter(s => {
      if (s.conditions.minInputSize && inputSize < s.conditions.minInputSize) return false;
      if (s.conditions.maxLatency && this.estimateLatency(input) > s.conditions.maxLatency) return false;
      if (s.conditions.maxEnergy && this.estimateEnergy(input) > s.conditions.maxEnergy) return false;
      return true;
    });

    // Select strategy based on priority
    if (priority === "latency") {
      return applicableStrategies.reduce((best, current) => 
        current.weight.latency > best.weight.latency ? current : best
      );
    } else if (priority === "energy") {
      return applicableStrategies.reduce((best, current) => 
        current.weight.energy > best.weight.energy ? current : best
      );
    } else if (priority === "compute") {
      return applicableStrategies.reduce((best, current) => 
        current.weight.compute > best.weight.compute ? current : best
      );
    } else {
      // Balanced approach
      return applicableStrategies.reduce((best, current) => 
        this.calculateStrategyScore(current) > this.calculateStrategyScore(best) ? current : best
      );
    }
  }

  /**
   * Applies integrated optimizations based on selected strategy
   */
  private async applyIntegratedOptimizations(
    operation: string,
    input: any,
    hologramFn: (input: any) => any,
    strategy: OptimizationStrategy,
    options: any
  ): Promise<{
    proofOptimization: ProofOptimizationResult | null;
    performanceOptimization: OptimizationResult | null;
    energyScaling: any;
  }> {
    const results: any = {
      proofOptimization: null,
      performanceOptimization: null,
      energyScaling: null
    };

    // Apply proof-based optimization if enabled
    if (this.config.enableCompressedProofs && strategy.weight.compression > 0.5) {
      results.proofOptimization = await this.compressedProofSystem.createCompressedProof(
        operation,
        input,
        hologramFn,
        {
          invariants: options.invariants,
          parentProofs: options.parentProofs,
          enableCompression: true
        }
      );
    }

    // Apply performance optimization if enabled
    if (this.config.enableProofBasedComputation || this.config.enableParallelProcessing) {
      results.performanceOptimization = await this.performanceOptimizer.optimizeHologramGeneration(
        input,
        hologramFn
      );
    }

    // Apply energy scaling if enabled
    if (this.config.enableEnergyOptimization && strategy.weight.energy > 0.5) {
      results.energyScaling = this.energyScaling.analyzeAndScale();
    }

    return results;
  }

  /**
   * Calculates total improvement from all optimizations
   */
  private calculateTotalImprovement(results: any): number {
    let totalImprovement = 0;
    let weightSum = 0;

    // Weight improvements based on strategy
    const weights = { latency: 0.3, energy: 0.3, compute: 0.2, compression: 0.2 };

    if (results.performanceOptimization) {
      totalImprovement += results.performanceOptimization.latencyImprovement * weights.latency;
      totalImprovement += results.performanceOptimization.energyImprovement * weights.energy;
      totalImprovement += results.performanceOptimization.computeImprovement * weights.compute;
      weightSum += weights.latency + weights.energy + weights.compute;
    }

    if (results.proofOptimization) {
      const compressionImprovement = (1 - results.proofOptimization.compressedProof.compressionRatio) * 100;
      totalImprovement += compressionImprovement * weights.compression;
      weightSum += weights.compression;
    }

    return weightSum > 0 ? totalImprovement / weightSum : 0;
  }

  /**
   * Calculates strategy score for balanced selection
   */
  private calculateStrategyScore(strategy: OptimizationStrategy): number {
    return (
      strategy.weight.latency * 0.3 +
      strategy.weight.energy * 0.3 +
      strategy.weight.compute * 0.2 +
      strategy.weight.compression * 0.2
    ) * strategy.priority;
  }

  /**
   * Initializes optimization strategies
   */
  private initializeOptimizationStrategies(): void {
    // Balanced strategy
    this.optimizationStrategies.set("balanced", {
      name: "balanced",
      priority: 1.0,
      weight: { latency: 0.7, energy: 0.7, compute: 0.6, compression: 0.5 },
      conditions: {}
    });

    // Latency-focused strategy
    this.optimizationStrategies.set("latency", {
      name: "latency",
      priority: 1.2,
      weight: { latency: 1.0, energy: 0.3, compute: 0.4, compression: 0.6 },
      conditions: { maxLatency: 50 }
    });

    // Energy-focused strategy
    this.optimizationStrategies.set("energy", {
      name: "energy",
      priority: 1.1,
      weight: { latency: 0.4, energy: 1.0, compute: 0.5, compression: 0.7 },
      conditions: { maxEnergy: 0.001 }
    });

    // Compute-focused strategy
    this.optimizationStrategies.set("compute", {
      name: "compute",
      priority: 1.0,
      weight: { latency: 0.5, energy: 0.4, compute: 1.0, compression: 0.8 },
      conditions: {}
    });

    // Holographic strategy
    this.optimizationStrategies.set("holographic", {
      name: "holographic",
      priority: 1.3,
      weight: { latency: 0.6, energy: 0.6, compute: 0.6, compression: 1.0 },
      conditions: { 
        requiredInvariants: ["holographic_correspondence"],
        minInputSize: 512
      }
    });

    // High-throughput strategy
    this.optimizationStrategies.set("throughput", {
      name: "throughput",
      priority: 1.1,
      weight: { latency: 0.8, energy: 0.5, compute: 0.8, compression: 0.4 },
      conditions: { minInputSize: 1024 }
    });
  }

  // Estimation methods
  private estimateLatency(input: any): number {
    return JSON.stringify(input).length * 0.1;
  }

  private estimateEnergy(input: any): number {
    return JSON.stringify(input).length * 0.001;
  }

  /**
   * Gets comprehensive optimization statistics
   */
  getOptimizationStats(): {
    totalOptimizations: number;
    averageTotalImprovement: number;
    strategyDistribution: Map<string, number>;
    performanceGains: {
      latency: number;
      energy: number;
      compute: number;
      compression: number;
    };
    optimizationEfficiency: number;
  } {
    const totalOptimizations = this.optimizationHistory.length;
    
    if (totalOptimizations === 0) {
      return {
        totalOptimizations: 0,
        averageTotalImprovement: 0,
        strategyDistribution: new Map(),
        performanceGains: { latency: 0, energy: 0, compute: 0, compression: 0 },
        optimizationEfficiency: 0
      };
    }

    // Calculate average total improvement
    const averageTotalImprovement = this.optimizationHistory.reduce(
      (sum, r) => sum + r.totalImprovement, 0
    ) / totalOptimizations;

    // Calculate strategy distribution
    const strategyDistribution = new Map<string, number>();
    for (const result of this.optimizationHistory) {
      const count = strategyDistribution.get(result.strategy) || 0;
      strategyDistribution.set(result.strategy, count + 1);
    }

    // Calculate average performance gains
    const avgLatency = this.optimizationHistory.reduce((sum, r) => sum + r.performanceGains.latency, 0) / totalOptimizations;
    const avgEnergy = this.optimizationHistory.reduce((sum, r) => sum + r.performanceGains.energy, 0) / totalOptimizations;
    const avgCompute = this.optimizationHistory.reduce((sum, r) => sum + r.performanceGains.compute, 0) / totalOptimizations;
    const avgCompression = this.optimizationHistory.reduce((sum, r) => sum + r.performanceGains.compression, 0) / totalOptimizations;

    // Calculate optimization efficiency
    const avgOptimizationTime = this.optimizationHistory.reduce((sum, r) => sum + r.optimizationTime, 0) / totalOptimizations;
    const optimizationEfficiency = averageTotalImprovement / Math.max(avgOptimizationTime, 1);

    return {
      totalOptimizations,
      averageTotalImprovement,
      strategyDistribution,
      performanceGains: {
        latency: avgLatency,
        energy: avgEnergy,
        compute: avgCompute,
        compression: avgCompression
      },
      optimizationEfficiency
    };
  }

  /**
   * Optimizes system configuration based on historical performance
   */
  async optimizeSystemConfiguration(): Promise<Partial<IntegratedOptimizationConfig>> {
    const stats = this.getOptimizationStats();
    const recommendations: Partial<IntegratedOptimizationConfig> = {};

    // Analyze performance patterns and recommend configuration changes
    if (stats.performanceGains.latency < 20) {
      recommendations.enableParallelProcessing = true;
      recommendations.maxConcurrency = Math.min(16, this.config.maxConcurrency * 1.5);
    }

    if (stats.performanceGains.energy < 15) {
      recommendations.enableEnergyOptimization = true;
      recommendations.energyThreshold = Math.max(0.0001, this.config.energyThreshold * 0.8);
    }

    if (stats.performanceGains.compression < 0.5) {
      recommendations.enableCompressedProofs = true;
      recommendations.enableHolographicCompression = true;
      recommendations.compressionRatio = Math.max(0.2, this.config.compressionRatio * 0.8);
    }

    if (stats.optimizationEfficiency < 0.5) {
      recommendations.enableAdaptiveCaching = true;
    }

    return recommendations;
  }
}

/**
 * Hologram Performance Optimization System
 * 
 * Comprehensive optimization system for minimizing latency, compute, and energy
 * requirements in hologram operations while maintaining holographic correspondence.
 */

export { HologramPerformanceOptimizer } from './HologramPerformanceOptimizer';
export { CompressedProofSystem } from './CompressedProofSystem';
export { IntegratedHologramOptimizer } from './IntegratedHologramOptimizer';
export { runHologramOptimizationExamples } from './examples/HologramOptimizationExample';

// Import types for internal use
import type { IntegratedOptimizationConfig, IntegratedHologramOptimizer } from './IntegratedHologramOptimizer';

// Re-export types for convenience
export type {
  OptimizationConfig,
  OptimizationResult,
  CompressedProof,
  ParallelExecutionPlan
} from './HologramPerformanceOptimizer';

export type {
  CompressedProofConfig,
  CompressedProofData,
  ProofOptimizationResult,
  HolographicCompression
} from './CompressedProofSystem';

export type {
  IntegratedOptimizationConfig,
  IntegratedOptimizationResult,
  OptimizationStrategy
} from './IntegratedHologramOptimizer';

/**
 * Quick setup function for common optimization scenarios
 */
export function createOptimizedHologramSystem(
  config: Partial<IntegratedOptimizationConfig> = {}
): IntegratedHologramOptimizer {
  const { Metrics } = require('../monitoring/metrics/Metrics');
  const { ProofChainManager } = require('../proof-chain/ProofChain');
  const { IntegratedHologramOptimizer } = require('./IntegratedHologramOptimizer');
  
  const metrics = new Metrics();
  const proofChainManager = new ProofChainManager(metrics);
  
  return new IntegratedHologramOptimizer(config, metrics, proofChainManager);
}

/**
 * Default optimization configurations for common use cases
 */
export const OptimizationPresets = {
  /**
   * Balanced optimization for general use
   */
  balanced: {
    enableProofBasedComputation: true,
    enableCompressedProofs: true,
    enableEnergyOptimization: true,
    enableParallelProcessing: true,
    enableAdaptiveCaching: true,
    optimizationStrategy: "balanced" as const,
    maxConcurrency: 8,
    energyThreshold: 0.0005,
    latencyThreshold: 100,
    compressionRatio: 0.3
  },

  /**
   * Latency-optimized configuration for real-time applications
   */
  latency: {
    enableProofBasedComputation: true,
    enableCompressedProofs: true,
    enableEnergyOptimization: false,
    enableParallelProcessing: true,
    enableAdaptiveCaching: true,
    optimizationStrategy: "latency" as const,
    maxConcurrency: 16,
    energyThreshold: 0.001,
    latencyThreshold: 50,
    compressionRatio: 0.4
  },

  /**
   * Energy-optimized configuration for battery-powered devices
   */
  energy: {
    enableProofBasedComputation: true,
    enableCompressedProofs: true,
    enableEnergyOptimization: true,
    enableParallelProcessing: false,
    enableAdaptiveCaching: true,
    optimizationStrategy: "energy" as const,
    maxConcurrency: 4,
    energyThreshold: 0.0002,
    latencyThreshold: 200,
    compressionRatio: 0.2
  },

  /**
   * High-throughput configuration for batch processing
   */
  throughput: {
    enableProofBasedComputation: true,
    enableCompressedProofs: true,
    enableEnergyOptimization: true,
    enableParallelProcessing: true,
    enableAdaptiveCaching: true,
    optimizationStrategy: "throughput" as const,
    maxConcurrency: 12,
    energyThreshold: 0.0008,
    latencyThreshold: 150,
    compressionRatio: 0.35
  },

  /**
   * Holographic-optimized configuration for data-intensive operations
   */
  holographic: {
    enableProofBasedComputation: true,
    enableCompressedProofs: true,
    enableEnergyOptimization: true,
    enableParallelProcessing: true,
    enableAdaptiveCaching: true,
    enableHolographicCompression: true,
    optimizationStrategy: "holographic" as const,
    maxConcurrency: 6,
    energyThreshold: 0.0006,
    latencyThreshold: 120,
    compressionRatio: 0.25
  }
} as const;

/**
 * Utility function to get optimization recommendations based on system characteristics
 */
export function getOptimizationRecommendations(
  systemCharacteristics: {
    cpuCores: number;
    memoryGB: number;
    energyConstraints: boolean;
    latencyRequirements: 'low' | 'medium' | 'high';
    throughputRequirements: 'low' | 'medium' | 'high';
  }
): Partial<IntegratedOptimizationConfig> {
  const { cpuCores, memoryGB, energyConstraints, latencyRequirements, throughputRequirements } = systemCharacteristics;
  
  const recommendations: Partial<IntegratedOptimizationConfig> = {
    enableProofBasedComputation: true,
    enableCompressedProofs: true,
    enableAdaptiveCaching: true
  };

  // Adjust concurrency based on CPU cores
  recommendations.maxConcurrency = Math.min(cpuCores * 2, 16);

  // Adjust energy optimization based on constraints
  if (energyConstraints) {
    recommendations.enableEnergyOptimization = true;
    recommendations.energyThreshold = 0.0003;
    recommendations.enableParallelProcessing = cpuCores > 4;
  } else {
    recommendations.enableEnergyOptimization = false;
    recommendations.enableParallelProcessing = true;
  }

  // Adjust latency thresholds based on requirements
  switch (latencyRequirements) {
    case 'low':
      recommendations.latencyThreshold = 50;
      recommendations.optimizationStrategy = 'latency';
      break;
    case 'medium':
      recommendations.latencyThreshold = 100;
      recommendations.optimizationStrategy = 'balanced';
      break;
    case 'high':
      recommendations.latencyThreshold = 200;
      recommendations.optimizationStrategy = 'energy';
      break;
  }

  // Adjust throughput settings
  switch (throughputRequirements) {
    case 'low':
      recommendations.maxConcurrency = Math.min(cpuCores, 4);
      break;
    case 'medium':
      recommendations.maxConcurrency = Math.min(cpuCores * 1.5, 8);
      break;
    case 'high':
      recommendations.maxConcurrency = Math.min(cpuCores * 2, 16);
      recommendations.optimizationStrategy = 'balanced';
      break;
  }

  // Adjust compression based on memory
  if (memoryGB < 4) {
    recommendations.compressionRatio = 0.2;
    recommendations.enableHolographicCompression = true;
  } else if (memoryGB < 8) {
    recommendations.compressionRatio = 0.3;
  } else {
    recommendations.compressionRatio = 0.4;
  }

  return recommendations;
}

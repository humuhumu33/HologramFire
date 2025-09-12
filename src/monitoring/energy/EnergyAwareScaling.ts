import { Metrics } from "../metrics/Metrics";
import { ccmHash } from "../../crypto/ccm/CCMHash";
import { stableStringify } from "../../crypto/util/stable";

/**
 * Energy-aware scaling algorithms for optimizing system performance
 * while maintaining holographic correspondence and energy efficiency
 */

export interface EnergyMetrics {
  cpuUtilization: number; // 0-1
  memoryUtilization: number; // 0-1
  energyConsumption: number; // Joules per operation
  thermalState: number; // 0-1 (0 = cool, 1 = hot)
  powerEfficiency: number; // operations per Joule
  holographic_correspondence: string;
}

export interface ScalingDecision {
  action: 'scale_up' | 'scale_down' | 'maintain' | 'throttle';
  factor: number; // scaling factor (0.1 - 2.0)
  reason: string;
  confidence: number; // 0-1
  energyImpact: number; // estimated energy change
  performanceImpact: number; // estimated performance change
  holographic_correspondence: string;
}

export interface ScalingConfig {
  enableEnergyOptimization: boolean;
  enableThermalManagement: boolean;
  enableAdaptiveScaling: boolean;
  energyThreshold: number; // Joules per operation threshold
  thermalThreshold: number; // thermal state threshold
  scalingWindow: number; // time window for scaling decisions (ms)
  minScalingFactor: number;
  maxScalingFactor: number;
  hysteresisFactor: number; // prevent oscillation
}

export interface ScalingHistory {
  timestamp: number;
  decision: ScalingDecision;
  metrics: EnergyMetrics;
  actualPerformance: number;
  actualEnergy: number;
}

export interface EnergyAwareScalingResult {
  currentMetrics: EnergyMetrics;
  scalingDecision: ScalingDecision;
  scalingHistory: ScalingHistory[];
  performanceGain: number;
  energySavings: number;
  holographic_correspondence: string;
}

/**
 * Energy-aware scaling engine
 */
export class EnergyAwareScaling {
  private config: ScalingConfig;
  private metrics: Metrics;
  private scalingHistory: ScalingHistory[] = [];
  private currentScalingFactor: number = 1.0;
  private lastScalingTime: number = 0;
  private energyModel: Map<string, number> = new Map();
  private performanceModel: Map<string, number> = new Map();

  constructor(config: Partial<ScalingConfig> = {}, metrics: Metrics) {
    this.config = {
      enableEnergyOptimization: config.enableEnergyOptimization !== false,
      enableThermalManagement: config.enableThermalManagement !== false,
      enableAdaptiveScaling: config.enableAdaptiveScaling !== false,
      energyThreshold: config.energyThreshold || 0.001, // 1mJ per operation
      thermalThreshold: config.thermalThreshold || 0.8,
      scalingWindow: config.scalingWindow || 30000, // 30 seconds
      minScalingFactor: config.minScalingFactor || 0.1,
      maxScalingFactor: config.maxScalingFactor || 2.0,
      hysteresisFactor: config.hysteresisFactor || 0.1
    };
    this.metrics = metrics;
    this.initializeEnergyModel();
  }

  /**
   * Analyzes current system state and makes scaling decisions
   */
  analyzeAndScale(): EnergyAwareScalingResult {
    const currentMetrics = this.collectEnergyMetrics();
    const scalingDecision = this.makeScalingDecision(currentMetrics);
    
    // Apply scaling decision
    this.applyScalingDecision(scalingDecision);
    
    // Record in history
    const historyEntry: ScalingHistory = {
      timestamp: Date.now(),
      decision: scalingDecision,
      metrics: currentMetrics,
      actualPerformance: this.estimatePerformance(scalingDecision),
      actualEnergy: this.estimateEnergy(scalingDecision)
    };
    this.scalingHistory.push(historyEntry);
    
    // Keep only recent history
    const cutoff = Date.now() - (this.config.scalingWindow * 10);
    this.scalingHistory = this.scalingHistory.filter(h => h.timestamp > cutoff);
    
    // Calculate gains
    const performanceGain = this.calculatePerformanceGain();
    const energySavings = this.calculateEnergySavings();
    
    return {
      currentMetrics,
      scalingDecision,
      scalingHistory: this.scalingHistory.slice(-10), // Last 10 decisions
      performanceGain,
      energySavings,
      holographic_correspondence: ccmHash({
        currentMetrics,
        scalingDecision,
        performanceGain,
        energySavings
      }, 'energy_aware_scaling')
    };
  }

  /**
   * Collects current energy and performance metrics
   */
  private collectEnergyMetrics(): EnergyMetrics {
    const snapshot = this.metrics.snapshot();
    
    // Estimate CPU utilization from operation rate
    const totalOperations = snapshot.counters['total_operations'] || 1;
    const timeWindow = this.config.scalingWindow;
    const operationsPerSecond = totalOperations / (timeWindow / 1000);
    const cpuUtilization = Math.min(1.0, operationsPerSecond / 1000); // Normalize to 0-1
    
    // Estimate memory utilization from gauge
    const memoryUtilization = Math.min(1.0, snapshot.gauges['memory_usage'] || 0.5);
    
    // Calculate energy consumption per operation
    const energyConsumption = this.calculateEnergyPerOperation(snapshot);
    
    // Estimate thermal state based on CPU utilization and energy consumption
    const thermalState = Math.min(1.0, (cpuUtilization * 0.7) + (energyConsumption * 1000 * 0.3));
    
    // Calculate power efficiency (operations per Joule)
    const powerEfficiency = energyConsumption > 0 ? 1.0 / energyConsumption : 1000;
    
    return {
      cpuUtilization,
      memoryUtilization,
      energyConsumption,
      thermalState,
      powerEfficiency,
      holographic_correspondence: ccmHash({
        cpuUtilization,
        memoryUtilization,
        energyConsumption,
        thermalState,
        powerEfficiency,
        timestamp: Date.now()
      }, 'energy_metrics')
    };
  }

  /**
   * Makes scaling decision based on current metrics
   */
  private makeScalingDecision(metrics: EnergyMetrics): ScalingDecision {
    const now = Date.now();
    
    // Check if enough time has passed since last scaling
    if (now - this.lastScalingTime < this.config.scalingWindow) {
      return {
        action: 'maintain',
        factor: this.currentScalingFactor,
        reason: 'Within scaling cooldown period',
        confidence: 0.9,
        energyImpact: 0,
        performanceImpact: 0,
        holographic_correspondence: ccmHash({
          action: 'maintain',
          reason: 'cooldown',
          timestamp: now
        }, 'scaling_decision')
      };
    }
    
    let action: ScalingDecision['action'] = 'maintain';
    let factor = this.currentScalingFactor;
    let reason = 'System operating within optimal range';
    let confidence = 0.5;
    
    // Energy optimization logic
    if (this.config.enableEnergyOptimization) {
      if (metrics.energyConsumption > this.config.energyThreshold) {
        // High energy consumption - consider scaling down
        if (metrics.cpuUtilization < 0.7) {
          action = 'scale_down';
          factor = Math.max(this.config.minScalingFactor, this.currentScalingFactor * 0.8);
          reason = 'High energy consumption with low CPU utilization';
          confidence = 0.8;
        } else if (metrics.thermalState > this.config.thermalThreshold) {
          action = 'throttle';
          factor = Math.max(this.config.minScalingFactor, this.currentScalingFactor * 0.6);
          reason = 'Thermal throttling due to high temperature';
          confidence = 0.9;
        }
      } else if (metrics.energyConsumption < this.config.energyThreshold * 0.5) {
        // Low energy consumption - consider scaling up
        if (metrics.cpuUtilization > 0.8 && metrics.thermalState < this.config.thermalThreshold * 0.8) {
          action = 'scale_up';
          factor = Math.min(this.config.maxScalingFactor, this.currentScalingFactor * 1.2);
          reason = 'Low energy consumption with high CPU utilization';
          confidence = 0.7;
        }
      }
    }
    
    // Thermal management logic
    if (this.config.enableThermalManagement && metrics.thermalState > this.config.thermalThreshold) {
      action = 'throttle';
      factor = Math.max(this.config.minScalingFactor, this.currentScalingFactor * 0.5);
      reason = 'Thermal management - reducing performance to cool down';
      confidence = 0.95;
    }
    
    // Adaptive scaling based on performance trends
    if (this.config.enableAdaptiveScaling) {
      const performanceTrend = this.analyzePerformanceTrend();
      if (performanceTrend === 'declining' && metrics.cpuUtilization < 0.6) {
        action = 'scale_up';
        factor = Math.min(this.config.maxScalingFactor, this.currentScalingFactor * 1.1);
        reason = 'Adaptive scaling up due to declining performance';
        confidence = 0.6;
      } else if (performanceTrend === 'improving' && metrics.energyConsumption > this.config.energyThreshold) {
        action = 'scale_down';
        factor = Math.max(this.config.minScalingFactor, this.currentScalingFactor * 0.9);
        reason = 'Adaptive scaling down due to improving performance with high energy';
        confidence = 0.6;
      }
    }
    
    // Apply hysteresis to prevent oscillation
    if (action !== 'maintain') {
      const lastDecision = this.scalingHistory[this.scalingHistory.length - 1];
      if (lastDecision && lastDecision.decision.action === action) {
        // Same action as last time - apply hysteresis
        factor = factor * (1 + this.config.hysteresisFactor);
        if (action === 'scale_up') {
          factor = Math.min(this.config.maxScalingFactor, factor);
        } else {
          factor = Math.max(this.config.minScalingFactor, factor);
        }
        reason += ' (hysteresis applied)';
      }
    }
    
    const energyImpact = this.estimateEnergyImpact(action, factor);
    const performanceImpact = this.estimatePerformanceImpact(action, factor);
    
    return {
      action,
      factor,
      reason,
      confidence,
      energyImpact,
      performanceImpact,
      holographic_correspondence: ccmHash({
        action,
        factor,
        reason,
        confidence,
        energyImpact,
        performanceImpact,
        timestamp: now
      }, 'scaling_decision')
    };
  }

  /**
   * Applies scaling decision to system
   */
  private applyScalingDecision(decision: ScalingDecision): void {
    if (decision.action !== 'maintain') {
      this.currentScalingFactor = decision.factor;
      this.lastScalingTime = Date.now();
      
      // Update metrics
      this.metrics.setGauge('scaling_factor', decision.factor);
      this.metrics.inc('scaling_actions_total', 1, { action: decision.action });
      
      // Log scaling event
      this.metrics.observe('scaling_energy_impact', decision.energyImpact);
      this.metrics.observe('scaling_performance_impact', decision.performanceImpact);
    }
  }

  /**
   * Calculates energy consumption per operation
   */
  private calculateEnergyPerOperation(snapshot: any): number {
    const totalOperations = snapshot.counters['total_operations'] || 1;
    const cpuTime = snapshot.gauges['cpu_time_ms'] || 1000;
    const memoryUsage = snapshot.gauges['memory_usage'] || 0.5;
    
    // Simple energy model: CPU time * CPU power + Memory usage * Memory power
    const cpuPower = 0.1; // 100mW per ms
    const memoryPower = 0.05; // 50mW per unit memory usage
    
    const totalEnergy = (cpuTime * cpuPower) + (memoryUsage * memoryPower);
    return totalEnergy / totalOperations;
  }

  /**
   * Estimates energy impact of scaling decision
   */
  private estimateEnergyImpact(action: ScalingDecision['action'], factor: number): number {
    const baseEnergy = 0.001; // 1mJ per operation baseline
    
    switch (action) {
      case 'scale_up':
        return baseEnergy * (factor - 1.0) * 0.8; // 80% efficiency
      case 'scale_down':
        return baseEnergy * (1.0 - factor) * 0.6; // 60% savings
      case 'throttle':
        return baseEnergy * (1.0 - factor) * 0.8; // 80% savings
      default:
        return 0;
    }
  }

  /**
   * Estimates performance impact of scaling decision
   */
  private estimatePerformanceImpact(action: ScalingDecision['action'], factor: number): number {
    switch (action) {
      case 'scale_up':
        return (factor - 1.0) * 0.9; // 90% efficiency
      case 'scale_down':
        return (1.0 - factor) * 0.7; // 70% impact
      case 'throttle':
        return (1.0 - factor) * 0.5; // 50% impact
      default:
        return 0;
    }
  }

  /**
   * Estimates performance after scaling
   */
  private estimatePerformance(decision: ScalingDecision): number {
    const basePerformance = 1000; // operations per second baseline
    return basePerformance * decision.factor * (1 + decision.performanceImpact);
  }

  /**
   * Estimates energy after scaling
   */
  private estimateEnergy(decision: ScalingDecision): number {
    const baseEnergy = 0.001; // 1mJ per operation baseline
    return baseEnergy * decision.factor * (1 - decision.energyImpact);
  }

  /**
   * Analyzes performance trend from history
   */
  private analyzePerformanceTrend(): 'improving' | 'declining' | 'stable' {
    if (this.scalingHistory.length < 3) return 'stable';
    
    const recent = this.scalingHistory.slice(-3);
    const performanceValues = recent.map(h => h.actualPerformance);
    
    const trend = performanceValues[2] - performanceValues[0];
    const threshold = performanceValues[0] * 0.05; // 5% threshold
    
    if (trend > threshold) return 'improving';
    if (trend < -threshold) return 'declining';
    return 'stable';
  }

  /**
   * Calculates performance gain from scaling
   */
  private calculatePerformanceGain(): number {
    if (this.scalingHistory.length < 2) return 0;
    
    const baseline = this.scalingHistory[0].actualPerformance;
    const current = this.scalingHistory[this.scalingHistory.length - 1].actualPerformance;
    
    return ((current - baseline) / baseline) * 100;
  }

  /**
   * Calculates energy savings from scaling
   */
  private calculateEnergySavings(): number {
    if (this.scalingHistory.length < 2) return 0;
    
    const baseline = this.scalingHistory[0].actualEnergy;
    const current = this.scalingHistory[this.scalingHistory.length - 1].actualEnergy;
    
    return ((baseline - current) / baseline) * 100;
  }

  /**
   * Initializes energy model for different operation types
   */
  private initializeEnergyModel(): void {
    // Energy consumption per operation type (Joules)
    this.energyModel.set('hash', 0.0001);
    this.energyModel.set('sign', 0.0002);
    this.energyModel.set('verify', 0.0003);
    this.energyModel.set('attest', 0.00015);
    
    // Performance baseline per operation type (operations per second)
    this.performanceModel.set('hash', 10000);
    this.performanceModel.set('sign', 5000);
    this.performanceModel.set('verify', 3000);
    this.performanceModel.set('attest', 6000);
  }

  /**
   * Gets current scaling state
   */
  getCurrentState(): {
    scalingFactor: number;
    lastScalingTime: number;
    historyLength: number;
    holographic_correspondence: string;
  } {
    return {
      scalingFactor: this.currentScalingFactor,
      lastScalingTime: this.lastScalingTime,
      historyLength: this.scalingHistory.length,
      holographic_correspondence: ccmHash({
        scalingFactor: this.currentScalingFactor,
        lastScalingTime: this.lastScalingTime,
        historyLength: this.scalingHistory.length,
        timestamp: Date.now()
      }, 'scaling_state')
    };
  }

  /**
   * Resets scaling state
   */
  reset(): void {
    this.currentScalingFactor = 1.0;
    this.lastScalingTime = 0;
    this.scalingHistory = [];
    this.metrics.setGauge('scaling_factor', 1.0);
  }
}

/**
 * Global energy-aware scaling instance
 */
let globalScalingInstance: EnergyAwareScaling | null = null;

/**
 * Get or create global energy-aware scaling instance
 */
export function getEnergyAwareScaling(config?: Partial<ScalingConfig>, metrics?: Metrics): EnergyAwareScaling {
  if (!globalScalingInstance) {
    if (!metrics) {
      throw new Error('Metrics instance required for energy-aware scaling');
    }
    globalScalingInstance = new EnergyAwareScaling(config, metrics);
  }
  return globalScalingInstance;
}

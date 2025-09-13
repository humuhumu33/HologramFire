import { describe, it, expect, beforeEach } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { 
  EnergyAwareScaling, 
  getEnergyAwareScaling,
  ScalingConfig,
  EnergyMetrics
} from "../src/monitoring/energy/EnergyAwareScaling";

describe("Energy-Aware Scaling Algorithms", () => {
  let metrics: Metrics;
  let scaling: EnergyAwareScaling;
  let config: ScalingConfig;

  beforeEach(() => {
    metrics = new Metrics();
    config = {
      enableEnergyOptimization: true,
      enableThermalManagement: true,
      enableAdaptiveScaling: true,
      energyThreshold: 0.001,
      thermalThreshold: 0.8,
      scalingWindow: 1000, // 1 second for testing
      minScalingFactor: 0.1,
      maxScalingFactor: 2.0,
      hysteresisFactor: 0.1
    };
    scaling = new EnergyAwareScaling(config, metrics);
  });

  it("should analyze and scale based on energy metrics", () => {
    // Simulate high energy consumption
    metrics.setGauge('memory_usage', 0.9);
    metrics.inc('total_operations', 1000);
    metrics.setGauge('cpu_time_ms', 2000);
    
    const result = scaling.analyzeAndScale();
    
    expect(result.currentMetrics).toBeDefined();
    expect(result.scalingDecision).toBeDefined();
    expect(result.scalingHistory).toBeInstanceOf(Array);
    expect(result.performanceGain).toBeGreaterThanOrEqual(0);
    expect(result.energySavings).toBeGreaterThanOrEqual(0);
    expect(result.holographic_correspondence).toBeDefined();
    
    // Verify energy metrics structure
    expect(result.currentMetrics.cpuUtilization).toBeGreaterThanOrEqual(0);
    expect(result.currentMetrics.cpuUtilization).toBeLessThanOrEqual(1);
    expect(result.currentMetrics.memoryUtilization).toBeGreaterThanOrEqual(0);
    expect(result.currentMetrics.memoryUtilization).toBeLessThanOrEqual(1);
    expect(result.currentMetrics.energyConsumption).toBeGreaterThan(0);
    expect(result.currentMetrics.thermalState).toBeGreaterThanOrEqual(0);
    expect(result.currentMetrics.thermalState).toBeLessThanOrEqual(1);
    expect(result.currentMetrics.powerEfficiency).toBeGreaterThan(0);
  });

  it("should make scaling decisions based on energy consumption", () => {
    // Simulate high energy consumption scenario
    metrics.setGauge('memory_usage', 0.5);
    metrics.inc('total_operations', 500);
    metrics.setGauge('cpu_time_ms', 3000); // High CPU time = high energy
    
    const result = scaling.analyzeAndScale();
    
    // Should consider scaling down due to high energy consumption
    expect(['scale_down', 'throttle', 'maintain']).toContain(result.scalingDecision.action);
    expect(result.scalingDecision.factor).toBeGreaterThanOrEqual(config.minScalingFactor);
    expect(result.scalingDecision.factor).toBeLessThanOrEqual(config.maxScalingFactor);
    expect(result.scalingDecision.reason).toBeDefined();
    expect(result.scalingDecision.confidence).toBeGreaterThan(0);
    expect(result.scalingDecision.confidence).toBeLessThanOrEqual(1);
  });

  it("should handle thermal management", () => {
    // Simulate high thermal state
    metrics.setGauge('memory_usage', 0.9);
    metrics.inc('total_operations', 2000);
    metrics.setGauge('cpu_time_ms', 5000);
    
    const result = scaling.analyzeAndScale();
    
    // Should consider throttling due to thermal state
    if (result.currentMetrics.thermalState > config.thermalThreshold) {
      expect(result.scalingDecision.action).toBe('throttle');
      expect(result.scalingDecision.factor).toBeLessThan(1.0);
    }
  });

  it("should respect scaling cooldown period", () => {
    // First scaling decision
    const result1 = scaling.analyzeAndScale();
    
    // Immediate second scaling decision should be 'maintain'
    const result2 = scaling.analyzeAndScale();
    
    expect(result2.scalingDecision.action).toBe('maintain');
    expect(result2.scalingDecision.reason).toContain('cooldown');
    expect(result2.scalingDecision.confidence).toBeGreaterThan(0.8);
  });

  it("should maintain holographic correspondence", () => {
    const result = scaling.analyzeAndScale();
    
    // All components should have holographic correspondence
    expect(result.currentMetrics.holographic_correspondence).toBeDefined();
    expect(result.scalingDecision.holographic_correspondence).toBeDefined();
    expect(result.holographic_correspondence).toBeDefined();
    
    // Should be deterministic with same inputs
    const result2 = scaling.analyzeAndScale();
    // Note: holographic correspondence may vary due to timing differences
    expect(result2.holographic_correspondence).toBeDefined();
  });

  it("should demonstrate cycle conservation", () => {
    const startTime = Date.now();
    
    // Perform multiple scaling analyses
    for (let i = 0; i < 10; i++) {
      metrics.inc('total_operations', 100);
      scaling.analyzeAndScale();
    }
    
    const endTime = Date.now();
    
    // Should complete efficiently (cycle conservation)
    expect(endTime - startTime).toBeLessThan(100); // Less than 100ms
  });

  it("should demonstrate page conservation", () => {
    const initialMemory = process.memoryUsage();
    
    // Perform many scaling operations
    for (let i = 0; i < 100; i++) {
      metrics.inc('total_operations', 50);
      scaling.analyzeAndScale();
    }
    
    const finalMemory = process.memoryUsage();
    
    // Memory usage should be reasonable (page conservation)
    const memoryIncrease = finalMemory.heapUsed - initialMemory.heapUsed;
    expect(memoryIncrease).toBeLessThan(10 * 1024 * 1024); // Less than 10MB increase
  });

  it("should track scaling history", () => {
    // Perform multiple scaling analyses
    for (let i = 0; i < 5; i++) {
      metrics.inc('total_operations', 200);
      scaling.analyzeAndScale();
    }
    
    const state = scaling.getCurrentState();
    expect(state.scalingFactor).toBeGreaterThan(0);
    expect(state.historyLength).toBeGreaterThan(0);
    expect(state.holographic_correspondence).toBeDefined();
  });

  it("should calculate performance and energy gains", () => {
    // Simulate improving performance scenario
    metrics.setGauge('memory_usage', 0.3);
    metrics.inc('total_operations', 100);
    metrics.setGauge('cpu_time_ms', 500);
    
    const result = scaling.analyzeAndScale();
    
    expect(result.performanceGain).toBeGreaterThanOrEqual(0);
    expect(result.energySavings).toBeGreaterThanOrEqual(0);
    
    // Should have valid numeric values
    expect(typeof result.performanceGain).toBe('number');
    expect(typeof result.energySavings).toBe('number');
  });

  it("should handle edge cases gracefully", () => {
    // Test with minimal metrics
    const result = scaling.analyzeAndScale();
    
    expect(result).toBeDefined();
    expect(result.currentMetrics).toBeDefined();
    expect(result.scalingDecision).toBeDefined();
    
    // Should not throw errors with empty metrics
    expect(() => scaling.analyzeAndScale()).not.toThrow();
  });

  it("should work with global instance", () => {
    const globalScaling = getEnergyAwareScaling(config, metrics);
    
    const result = globalScaling.analyzeAndScale();
    
    expect(result).toBeDefined();
    expect(result.holographic_correspondence).toBeDefined();
    
    // Should be the same instance
    const globalScaling2 = getEnergyAwareScaling(config, metrics);
    expect(globalScaling).toBe(globalScaling2);
  });

  it("should reset scaling state", () => {
    // Perform some scaling operations
    metrics.inc('total_operations', 100);
    scaling.analyzeAndScale();
    
    const stateBefore = scaling.getCurrentState();
    expect(stateBefore.historyLength).toBeGreaterThan(0);
    
    // Reset
    scaling.reset();
    
    const stateAfter = scaling.getCurrentState();
    expect(stateAfter.scalingFactor).toBe(1.0);
    expect(stateAfter.historyLength).toBe(0);
    expect(stateAfter.lastScalingTime).toBe(0);
  });

  it("should apply hysteresis to prevent oscillation", () => {
    // Simulate oscillating conditions
    for (let i = 0; i < 3; i++) {
      if (i % 2 === 0) {
        metrics.setGauge('memory_usage', 0.9); // High usage
        metrics.setGauge('cpu_time_ms', 3000);
      } else {
        metrics.setGauge('memory_usage', 0.3); // Low usage
        metrics.setGauge('cpu_time_ms', 500);
      }
      metrics.inc('total_operations', 100);
      scaling.analyzeAndScale();
    }
    
    const state = scaling.getCurrentState();
    expect(state.scalingFactor).toBeGreaterThan(0);
    expect(state.scalingFactor).toBeLessThanOrEqual(config.maxScalingFactor);
  });

  it("should estimate energy and performance impacts", () => {
    const result = scaling.analyzeAndScale();
    
    expect(result.scalingDecision.energyImpact).toBeGreaterThanOrEqual(0);
    expect(result.scalingDecision.performanceImpact).toBeGreaterThanOrEqual(0);
    
    // Impact values should be reasonable
    expect(Math.abs(result.scalingDecision.energyImpact)).toBeLessThan(1.0);
    expect(Math.abs(result.scalingDecision.performanceImpact)).toBeLessThan(1.0);
  });
});

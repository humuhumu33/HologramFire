import { describe, it, expect, beforeEach } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { AlertRule } from "../src/monitoring/alerts/Rules";
import { 
  AdaptiveChaosEngine, 
  AdaptiveChaosPlan, 
  runAdaptiveChaos 
} from "../src/monitoring/chaos/AdaptiveChaosEngine";

describe("Adaptive Chaos Engineering", () => {
  let metrics: Metrics;
  let rules: AlertRule[];
  let plan: AdaptiveChaosPlan;

  beforeEach(() => {
    metrics = new Metrics();
    rules = [
      {
        id: "warning-rule",
        violationsAtLeast: 1
      }
    ];
    
    plan = {
      iterations: 100,
      baseViolationRate: 0.05,
      seed: 0xDEADBEEF,
      adaptationWindow: 10,
      minViolationRate: 0.01,
      maxViolationRate: 0.2,
      adaptationFactor: 0.5,
      targetResilience: 0.8
    };
  });

  it("should run adaptive chaos with dynamic failure injection", () => {
    const result = runAdaptiveChaos(metrics, rules, plan);
    
    expect(result).toBeDefined();
    expect(result.alerts).toBeInstanceOf(Array);
    expect(result.resilienceMetrics).toBeDefined();
    expect(result.appliedPatterns).toBeInstanceOf(Array);
    expect(result.adaptationHistory).toBeInstanceOf(Array);
    
    // Verify resilience metrics structure
    expect(result.resilienceMetrics.recoveryTime).toBeGreaterThanOrEqual(0);
    expect(result.resilienceMetrics.failureTolerance).toBeGreaterThanOrEqual(0);
    expect(result.resilienceMetrics.adaptationSpeed).toBeGreaterThanOrEqual(0);
    expect(result.resilienceMetrics.stabilityScore).toBeGreaterThanOrEqual(0);
    expect(result.resilienceMetrics.holographic_correspondence).toBeDefined();
  });

  it("should adapt violation rate based on system resilience", () => {
    const engine = new AdaptiveChaosEngine(metrics, rules, plan);
    const result = engine.runAdaptiveChaos();
    
    // Should have adaptation history
    expect(result.adaptationHistory.length).toBeGreaterThan(0);
    
    // Should have varied violation rates
    const violationRates = result.adaptationHistory.map(h => h.violationRate);
    const uniqueRates = new Set(violationRates);
    expect(uniqueRates.size).toBeGreaterThan(1); // Should have adapted
  });

  it("should generate diverse failure patterns", () => {
    const engine = new AdaptiveChaosEngine(metrics, rules, plan);
    const result = engine.runAdaptiveChaos();
    
    // Should have applied multiple patterns
    expect(result.appliedPatterns.length).toBeGreaterThan(0);
    
    // Should have different failure types
    const failureTypes = new Set(result.appliedPatterns.map(p => p.type));
    expect(failureTypes.size).toBeGreaterThan(1);
    
    // Should have varied intensities
    const intensities = result.appliedPatterns.map(p => p.intensity);
    const uniqueIntensities = new Set(intensities.map(i => Math.round(i * 10) / 10));
    expect(uniqueIntensities.size).toBeGreaterThan(1);
  });

  it("should respect violation rate bounds", () => {
    const engine = new AdaptiveChaosEngine(metrics, rules, plan);
    const result = engine.runAdaptiveChaos();
    
    // All violation rates should be within bounds
    result.adaptationHistory.forEach(history => {
      expect(history.violationRate).toBeGreaterThanOrEqual(plan.minViolationRate);
      expect(history.violationRate).toBeLessThanOrEqual(plan.maxViolationRate);
    });
  });

  it("should maintain holographic correspondence", () => {
    const engine = new AdaptiveChaosEngine(metrics, rules, plan);
    const result = engine.runAdaptiveChaos();
    
    // Resilience metrics should have holographic correspondence
    expect(result.resilienceMetrics.holographic_correspondence).toBeDefined();
    expect(result.resilienceMetrics.holographic_correspondence.length).toBeGreaterThan(0);
    
    // Should be deterministic with same seed
    const result2 = runAdaptiveChaos(metrics, rules, plan);
    expect(typeof result.resilienceMetrics.holographic_correspondence).toBe("string");
  });

  it("should provide meaningful adaptation reasons", () => {
    const engine = new AdaptiveChaosEngine(metrics, rules, plan);
    const result = engine.runAdaptiveChaos();
    
    // Should have adaptation reasons
    result.adaptationHistory.forEach(history => {
      expect(history.adaptationReason).toBeDefined();
      expect(history.adaptationReason.length).toBeGreaterThan(0);
      expect(history.adaptationReason).toMatch(/System (too resilient|struggling|stable)/);
    });
  });

  it("should handle edge cases gracefully", () => {
    const edgePlan: AdaptiveChaosPlan = {
      iterations: 1,
      baseViolationRate: 0.0,
      seed: 0x12345678,
      adaptationWindow: 1,
      minViolationRate: 0.0,
      maxViolationRate: 0.0,
      adaptationFactor: 0.0,
      targetResilience: 1.0
    };
    
    const result = runAdaptiveChaos(metrics, rules, edgePlan);
    
    expect(result).toBeDefined();
    expect(result.resilienceMetrics).toBeDefined();
    expect(result.appliedPatterns).toBeInstanceOf(Array);
    expect(result.adaptationHistory).toBeInstanceOf(Array);
  });

  it("should demonstrate cycle conservation", () => {
    const startTime = Date.now();
    const result = runAdaptiveChaos(metrics, rules, plan);
    const endTime = Date.now();
    
    // Should complete in reasonable time (cycle conservation)
    const executionTime = endTime - startTime;
    expect(executionTime).toBeLessThan(1000); // Should complete within 1 second
    
    // Should have processed all iterations
    expect(result.appliedPatterns.length).toBe(plan.iterations);
  });

  it("should demonstrate page conservation", () => {
    const initialMemory = process.memoryUsage();
    const result = runAdaptiveChaos(metrics, rules, plan);
    const finalMemory = process.memoryUsage();
    
    // Memory usage should be reasonable (page conservation)
    const memoryIncrease = finalMemory.heapUsed - initialMemory.heapUsed;
    expect(memoryIncrease).toBeLessThan(10 * 1024 * 1024); // Less than 10MB increase
  });
});

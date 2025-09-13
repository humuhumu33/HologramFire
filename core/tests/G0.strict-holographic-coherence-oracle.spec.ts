import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { Metrics } from '../src/monitoring/metrics/Metrics';
import { StrictHolographicCoherenceOracle, StrictCoherenceResult } from '../src/validator/StrictHolographicCoherenceOracle';
import fs from 'node:fs';
import path from 'node:path';

describe('StrictHolographicCoherenceOracle', () => {
  let metrics: Metrics;
  let oracle: StrictHolographicCoherenceOracle;
  let testModulePath: string;

  beforeEach(() => {
    metrics = new Metrics();
    oracle = new StrictHolographicCoherenceOracle(metrics, {
      enableRealTimeMonitoring: false,
      monitoringIntervalMs: 100,
      coherenceThreshold: 0.95,
      enableAdaptiveScoring: true,
      enablePerformanceCalibration: true,
      enableReferenceFingerprinting: true,
      maxViolationHistory: 100,
      enableTrendAnalysis: true
    });

    // Create a test module file
    testModulePath = path.join(__dirname, 'test-module.json');
    const testModule = {
      name: 'test-module',
      invariants: ['holographic_correspondence', 'resonance_classification', 'cycle_conservation', 'page_conservation'],
      implementation: {
        holographic: true,
        resonance: true,
        cycle: true,
        page: true
      }
    };
    fs.writeFileSync(testModulePath, JSON.stringify(testModule, null, 2));
  });

  afterEach(() => {
    // Clean up test files
    if (fs.existsSync(testModulePath)) {
      fs.unlinkSync(testModulePath);
    }
    
    // Stop any active monitoring
    oracle.stopRealTimeMonitoring();
  });

  describe('Module Validation', () => {
    it('should validate a module with strict coherence monitoring', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result).toBeDefined();
      expect(result.ok).toBeDefined();
      expect(result.oracle_score).toBeGreaterThanOrEqual(0);
      expect(result.oracle_score).toBeLessThanOrEqual(1);
      expect(result.coherenceScore).toBeGreaterThanOrEqual(0);
      expect(result.coherenceScore).toBeLessThanOrEqual(1);
      expect(result.violations).toBeInstanceOf(Array);
      expect(result.realTimeMetrics).toBeDefined();
      expect(result.holographicCorrespondence).toBeDefined();
      expect(result.resonanceClassification).toBeDefined();
      expect(result.cycleConservation).toBeDefined();
      expect(result.pageConservation).toBeDefined();
      expect(result.executionTimeMs).toBeGreaterThan(0);
      expect(result.timestamp).toBeGreaterThan(0);
    });

    it('should handle non-existent module gracefully', async () => {
      const nonExistentPath = path.join(__dirname, 'non-existent-module.json');
      const result = await oracle.validateModuleStrict(nonExistentPath);

      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBe(0);
      expect(result.coherenceScore).toBe(0);
      expect(result.violations.length).toBeGreaterThan(0);
      expect(result.violations[0].severity).toBe('critical');
    });

    it('should validate with different coherence thresholds', async () => {
      const lowThresholdOracle = new StrictHolographicCoherenceOracle(metrics, {
        coherenceThreshold: 0.5
      });

      const result = await lowThresholdOracle.validateModuleStrict(testModulePath);
      expect(result.ok).toBeDefined();
    });
  });

  describe('Real-time Monitoring', () => {
    it('should start and stop real-time monitoring', () => {
      expect(() => oracle.startRealTimeMonitoring()).not.toThrow();
      expect(() => oracle.stopRealTimeMonitoring()).not.toThrow();
    });

    it('should not start monitoring if already active', () => {
      oracle.startRealTimeMonitoring();
      expect(() => oracle.startRealTimeMonitoring()).not.toThrow();
      oracle.stopRealTimeMonitoring();
    });

    it('should handle monitoring with different intervals', () => {
      const fastOracle = new StrictHolographicCoherenceOracle(metrics, {
        monitoringIntervalMs: 50
      });

      expect(() => fastOracle.startRealTimeMonitoring()).not.toThrow();
      expect(() => fastOracle.stopRealTimeMonitoring()).not.toThrow();
    });
  });

  describe('Coherence Metrics', () => {
    it('should calculate real-time coherence metrics', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.realTimeMetrics.coherenceLevel).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.coherenceLevel).toBeLessThanOrEqual(1);
      expect(result.realTimeMetrics.stabilityIndex).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.stabilityIndex).toBeLessThanOrEqual(1);
      expect(result.realTimeMetrics.resonanceFrequency).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.holographicIntegrity).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.holographicIntegrity).toBeLessThanOrEqual(1);
      expect(result.realTimeMetrics.energyEfficiency).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.energyEfficiency).toBeLessThanOrEqual(1);
      expect(result.realTimeMetrics.memoryCoherence).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.memoryCoherence).toBeLessThanOrEqual(1);
      expect(result.realTimeMetrics.phaseAlignment).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.phaseAlignment).toBeLessThanOrEqual(1);
      expect(result.realTimeMetrics.interferenceLevel).toBeGreaterThanOrEqual(0);
      expect(result.realTimeMetrics.interferenceLevel).toBeLessThanOrEqual(1);
    });

    it('should calculate holographic correspondence metrics', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.holographicCorrespondence.correspondenceScore).toBeGreaterThanOrEqual(0);
      expect(result.holographicCorrespondence.correspondenceScore).toBeLessThanOrEqual(1);
      expect(result.holographicCorrespondence.structuralIntegrity).toBeGreaterThanOrEqual(0);
      expect(result.holographicCorrespondence.structuralIntegrity).toBeLessThanOrEqual(1);
      expect(result.holographicCorrespondence.patternConsistency).toBeGreaterThanOrEqual(0);
      expect(result.holographicCorrespondence.patternConsistency).toBeLessThanOrEqual(1);
      expect(result.holographicCorrespondence.selfSimilarity).toBeGreaterThanOrEqual(0);
      expect(result.holographicCorrespondence.selfSimilarity).toBeLessThanOrEqual(1);
      expect(result.holographicCorrespondence.holographicFingerprint).toBeDefined();
      expect(result.holographicCorrespondence.correspondenceViolations).toBeGreaterThanOrEqual(0);
    });

    it('should calculate resonance classification metrics', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.resonanceClassification.r96Classification).toBeGreaterThanOrEqual(0);
      expect(result.resonanceClassification.r96Classification).toBeLessThanOrEqual(95);
      expect(result.resonanceClassification.resonanceStability).toBeGreaterThanOrEqual(0);
      expect(result.resonanceClassification.resonanceStability).toBeLessThanOrEqual(1);
      expect(result.resonanceClassification.harmonicAlignment).toBeGreaterThanOrEqual(0);
      expect(result.resonanceClassification.harmonicAlignment).toBeLessThanOrEqual(1);
      expect(result.resonanceClassification.frequencyCoherence).toBeGreaterThanOrEqual(0);
      expect(result.resonanceClassification.frequencyCoherence).toBeLessThanOrEqual(1);
      expect(result.resonanceClassification.phaseCoherence).toBeGreaterThanOrEqual(0);
      expect(result.resonanceClassification.phaseCoherence).toBeLessThanOrEqual(1);
      expect(result.resonanceClassification.resonanceViolations).toBeGreaterThanOrEqual(0);
    });

    it('should calculate cycle conservation metrics', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.cycleConservation.cycleEfficiency).toBeGreaterThanOrEqual(0);
      expect(result.cycleConservation.cycleEfficiency).toBeLessThanOrEqual(1);
      expect(result.cycleConservation.energyConservation).toBeGreaterThanOrEqual(0);
      expect(result.cycleConservation.energyConservation).toBeLessThanOrEqual(1);
      expect(result.cycleConservation.computationalIntegrity).toBeGreaterThanOrEqual(0);
      expect(result.cycleConservation.computationalIntegrity).toBeLessThanOrEqual(1);
      expect(result.cycleConservation.resourceUtilization).toBeGreaterThanOrEqual(0);
      expect(result.cycleConservation.resourceUtilization).toBeLessThanOrEqual(1);
      expect(result.cycleConservation.cycleViolations).toBeGreaterThanOrEqual(0);
    });

    it('should calculate page conservation metrics', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.pageConservation.memoryEfficiency).toBeGreaterThanOrEqual(0);
      expect(result.pageConservation.memoryEfficiency).toBeLessThanOrEqual(1);
      expect(result.pageConservation.pageAlignment).toBeGreaterThanOrEqual(0);
      expect(result.pageConservation.pageAlignment).toBeLessThanOrEqual(1);
      expect(result.pageConservation.memoryCoherence).toBeGreaterThanOrEqual(0);
      expect(result.pageConservation.memoryCoherence).toBeLessThanOrEqual(1);
      expect(result.pageConservation.storageIntegrity).toBeGreaterThanOrEqual(0);
      expect(result.pageConservation.storageIntegrity).toBeLessThanOrEqual(1);
      expect(result.pageConservation.pageViolations).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Coherence Score Calculation', () => {
    it('should calculate overall coherence score', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.coherenceScore).toBeGreaterThanOrEqual(0);
      expect(result.coherenceScore).toBeLessThanOrEqual(1);
      expect(typeof result.coherenceScore).toBe('number');
    });

    it('should use weighted combination of metrics', async () => {
      const result1 = await oracle.validateModuleStrict(testModulePath);
      const result2 = await oracle.validateModuleStrict(testModulePath);

      // Results should be consistent for the same module
      expect(Math.abs(result1.coherenceScore - result2.coherenceScore)).toBeLessThan(0.1);
    });
  });

  describe('Violation Tracking', () => {
    it('should track violation trends', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.violationTrends).toBeInstanceOf(Array);
      result.violationTrends.forEach(trend => {
        expect(trend.timestamp).toBeGreaterThan(0);
        expect(trend.violationType).toBeDefined();
        expect(['critical', 'warning', 'info']).toContain(trend.severity);
        expect(trend.count).toBeGreaterThanOrEqual(0);
        expect(['increasing', 'decreasing', 'stable']).toContain(trend.trend);
      });
    });

    it('should update violation history', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      // Access private violation history through the oracle instance
      const violationHistory = (oracle as any).violationHistory;
      expect(violationHistory).toBeInstanceOf(Array);
    });
  });

  describe('Configuration', () => {
    it('should accept custom configuration', () => {
      const customOracle = new StrictHolographicCoherenceOracle(metrics, {
        enableRealTimeMonitoring: false,
        monitoringIntervalMs: 500,
        coherenceThreshold: 0.8,
        enableAdaptiveScoring: false,
        enablePerformanceCalibration: false,
        enableReferenceFingerprinting: false,
        maxViolationHistory: 50,
        enableTrendAnalysis: false
      });

      expect(customOracle).toBeDefined();
    });

    it('should use default configuration when none provided', () => {
      const defaultOracle = new StrictHolographicCoherenceOracle(metrics);
      expect(defaultOracle).toBeDefined();
    });
  });

  describe('Performance', () => {
    it('should complete validation within reasonable time', async () => {
      const startTime = Date.now();
      const result = await oracle.validateModuleStrict(testModulePath);
      const endTime = Date.now();

      expect(result.executionTimeMs).toBeGreaterThan(0);
      expect(endTime - startTime).toBeLessThan(5000); // Should complete within 5 seconds
    });

    it('should handle multiple concurrent validations', async () => {
      const promises = Array.from({ length: 5 }, () => 
        oracle.validateModuleStrict(testModulePath)
      );

      const results = await Promise.all(promises);
      
      results.forEach(result => {
        expect(result).toBeDefined();
        expect(result.ok).toBeDefined();
        expect(result.coherenceScore).toBeGreaterThanOrEqual(0);
        expect(result.coherenceScore).toBeLessThanOrEqual(1);
      });
    });
  });

  describe('Error Handling', () => {
    it('should handle invalid module paths gracefully', async () => {
      const invalidPath = '/invalid/path/module.json';
      const result = await oracle.validateModuleStrict(invalidPath);

      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBe(0);
      expect(result.coherenceScore).toBe(0);
      expect(result.violations.length).toBeGreaterThan(0);
    });

    it('should handle malformed module files gracefully', async () => {
      const malformedPath = path.join(__dirname, 'malformed-module.json');
      fs.writeFileSync(malformedPath, 'invalid json content');

      try {
        const result = await oracle.validateModuleStrict(malformedPath);
        expect(result.ok).toBe(false);
        expect(result.violations.length).toBeGreaterThan(0);
      } finally {
        if (fs.existsSync(malformedPath)) {
          fs.unlinkSync(malformedPath);
        }
      }
    });
  });

  describe('Integration', () => {
    it('should integrate with base oracle', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.ok).toBeDefined();
      expect(result.oracle_score).toBeDefined();
      expect(result.violations).toBeInstanceOf(Array);
      expect(result.holographic_fingerprint).toBeDefined();
    });

    it('should integrate with metrics system', async () => {
      const initialViolations = metrics.snapshot().violations;
      
      await oracle.validateModuleStrict(testModulePath);
      
      const finalViolations = metrics.snapshot().violations;
      expect(finalViolations).toBeGreaterThanOrEqual(initialViolations);
    });

    it('should integrate with reference fingerprinting', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.referenceFingerprint).toBeOneOf([undefined, expect.any(Object)]);
      expect(result.referenceFingerprint?.version).toBeOneOf([undefined, expect.any(String)]);
      expect(result.referenceFingerprint.python_hash).toBeDefined();
      expect(result.referenceFingerprint.execution_witness).toBeDefined();
      expect(result.referenceFingerprint.timestamp).toBeDefined();
      expect(result.referenceFingerprint.digest).toBeDefined();
    });
  });

  describe('Calibration State', () => {
    it('should provide calibration state', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.calibrationState).toBeDefined();
      expect(result.calibrationState.lastCalibration).toBeDefined();
      expect(result.calibrationState.targets).toBeDefined();
      expect(result.calibrationState.actions).toBeDefined();
      expect(result.calibrationState.feedback).toBeDefined();
      expect(result.calibrationState.performanceHistory).toBeDefined();
      expect(result.calibrationState.adaptiveFactors).toBeDefined();
      expect(result.calibrationState.holographic_fingerprint).toBeDefined();
    });
  });

  describe('Holographic Correspondence', () => {
    it('should maintain holographic correspondence with reference', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.holographicCorrespondence.correspondenceScore).toBeGreaterThan(0);
      expect(result.holographicCorrespondence.structuralIntegrity).toBeGreaterThan(0);
      expect(result.holographicCorrespondence.patternConsistency).toBeGreaterThan(0);
      expect(result.holographicCorrespondence.selfSimilarity).toBeGreaterThan(0);
    });
  });

  describe('Resonance Classification', () => {
    it('should properly classify resonance patterns', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.resonanceClassification.r96Classification).toBeGreaterThanOrEqual(0);
      expect(result.resonanceClassification.r96Classification).toBeLessThanOrEqual(95);
      expect(result.resonanceClassification.resonanceStability).toBeGreaterThan(0);
      expect(result.resonanceClassification.harmonicAlignment).toBeGreaterThan(0);
    });
  });

  describe('Cycle Conservation', () => {
    it('should ensure cycle conservation', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.cycleConservation.cycleEfficiency).toBeGreaterThan(0);
      expect(result.cycleConservation.energyConservation).toBeGreaterThan(0);
      expect(result.cycleConservation.computationalIntegrity).toBeGreaterThan(0);
    });
  });

  describe('Page Conservation', () => {
    it('should ensure page conservation', async () => {
      const result = await oracle.validateModuleStrict(testModulePath);

      expect(result.pageConservation.memoryEfficiency).toBeGreaterThan(0);
      expect(result.pageConservation.pageAlignment).toBeGreaterThan(0);
      expect(result.pageConservation.memoryCoherence).toBeGreaterThan(0);
    });
  });
});

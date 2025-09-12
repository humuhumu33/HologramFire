import { describe, it, expect, beforeEach, afterEach } from "vitest";
import path from "node:path";
import { EnhancedHologramOracle, EnhancedOracleConfig } from "../src/validator/EnhancedHologramOracle";
import { DynamicReferenceFingerprint } from "../src/validator/ReferenceFingerprint";
import { InvariantVerifier } from "../src/validator/InvariantVerifier";
import { AdaptiveOracleScoring } from "../src/validator/AdaptiveOracleScoring";
import { PerformanceCalibration } from "../src/validator/PerformanceCalibration";
import { Metrics } from "../src/monitoring/metrics/Metrics";

const goodModule = path.resolve("modules/example-good.json");
const badModule = path.resolve("modules/example-bad.json");
const blueprint = path.resolve("atlas-12288/blueprint/blueprint.json");

describe("G0: Enhanced Hologram Oracle System", () => {
  let oracle: EnhancedHologramOracle;
  let config: EnhancedOracleConfig;

  beforeEach(() => {
    config = {
      enableDynamicFingerprinting: true,
      enableInvariantVerification: true,
      enableAdaptiveScoring: true,
      enablePerformanceCalibration: true,
      enableMLOptimization: false,
      threshold: 0.95,
      maxViolations: 10,
      referenceFingerprintPath: "hologram_generator_mini.py",
      calibrationIntervalMs: 1000, // Fast for testing
      performanceWindowMs: 5000 // Short window for testing
    };
    oracle = new EnhancedHologramOracle(config);
  });

  afterEach(() => {
    oracle.clearCaches();
  });

  describe("Enhanced Module Validation", () => {
    it("validates good module with all enhancements", async () => {
      const result = await oracle.validateModule(goodModule);
      
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThanOrEqual(0.95);
      expect(result.execution_time_ms).toBeGreaterThan(0);
      expect(result.referenceFingerprint).toBeDefined();
      expect(result.invariantVerifications).toBeDefined();
      expect(result.adaptiveScoring).toBeDefined();
      expect(result.calibrationState).toBeDefined();
      expect(result.holographic_correspondence).toBeTruthy();
    });

    it("identifies violations in bad module with enhanced analysis", async () => {
      const result = await oracle.validateModule(badModule);
      
      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBeLessThan(0.95);
      expect(result.violations.length).toBeGreaterThan(0);
      expect(result.execution_time_ms).toBeGreaterThan(0);
      
      // Should have enhanced analysis even for bad modules
      expect(result.referenceFingerprint).toBeDefined();
      expect(result.invariantVerifications).toBeDefined();
      expect(result.adaptiveScoring).toBeDefined();
      expect(result.calibrationState).toBeDefined();
    });

    it("provides detailed invariant verification results", async () => {
      const result = await oracle.validateModule(goodModule);
      
      expect(result.invariantVerifications).toBeInstanceOf(Array);
      result.invariantVerifications.forEach(verification => {
        expect(verification.invariant).toBeTruthy();
        expect(verification.verified).toBeDefined();
        expect(verification.confidence).toBeGreaterThanOrEqual(0);
        expect(verification.confidence).toBeLessThanOrEqual(1);
        expect(verification.evidence).toBeDefined();
        expect(verification.holographic_correspondence).toBeTruthy();
        expect(verification.execution_time_ms).toBeGreaterThanOrEqual(0);
      });
    });

    it("provides adaptive scoring with weighted components", async () => {
      const result = await oracle.validateModule(goodModule);
      
      expect(result.adaptiveScoring.overallScore).toBeGreaterThanOrEqual(0);
      expect(result.adaptiveScoring.overallScore).toBeLessThanOrEqual(1);
      expect(result.adaptiveScoring.components).toBeInstanceOf(Array);
      expect(result.adaptiveScoring.confidence).toBeGreaterThanOrEqual(0);
      expect(result.adaptiveScoring.confidence).toBeLessThanOrEqual(1);
      expect(result.adaptiveScoring.threshold).toBeGreaterThan(0);
      expect(result.adaptiveScoring.recommendation).toBeDefined();
      expect(result.adaptiveScoring.adaptive_factors).toBeDefined();
      
      result.adaptiveScoring.components.forEach(component => {
        expect(component.name).toBeTruthy();
        expect(component.weight).toBeGreaterThan(0);
        expect(component.score).toBeGreaterThanOrEqual(0);
        expect(component.score).toBeLessThanOrEqual(1);
        expect(component.confidence).toBeGreaterThanOrEqual(0);
        expect(component.confidence).toBeLessThanOrEqual(1);
        expect(component.evidence).toBeDefined();
        expect(component.holographic_correspondence).toBeTruthy();
      });
    });

    it("provides performance calibration state", async () => {
      const result = await oracle.validateModule(goodModule);
      
      expect(result.calibrationState.targets).toBeInstanceOf(Map);
      expect(result.calibrationState.actions).toBeInstanceOf(Array);
      expect(result.calibrationState.feedback).toBeInstanceOf(Array);
      expect(result.calibrationState.performanceHistory).toBeInstanceOf(Array);
      expect(result.calibrationState.adaptiveFactors).toBeDefined();
      expect(result.calibrationState.holographic_fingerprint).toBeTruthy();
      expect(result.calibrationState.lastCalibration).toBeTruthy();
    });
  });

  describe("Enhanced Blueprint Validation", () => {
    it("validates blueprint with all enhancements", async () => {
      const result = await oracle.validateBlueprint(blueprint);
      
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThanOrEqual(0.95);
      expect(result.execution_time_ms).toBeGreaterThan(0);
      expect(result.referenceFingerprint).toBeDefined();
      expect(result.invariantVerifications).toBeDefined();
      expect(result.adaptiveScoring).toBeDefined();
      expect(result.calibrationState).toBeDefined();
      expect(result.holographic_correspondence).toBeTruthy();
    });
  });

  describe("Configuration Management", () => {
    it("allows disabling individual enhancements", async () => {
      const disabledConfig: EnhancedOracleConfig = {
        enableDynamicFingerprinting: false,
        enableInvariantVerification: false,
        enableAdaptiveScoring: false,
        enablePerformanceCalibration: false,
        enableMLOptimization: false,
        threshold: 0.95,
        maxViolations: 10,
        calibrationIntervalMs: 5000,
        performanceWindowMs: 10000,
        referenceFingerprintPath: ""
      };
      
      const disabledOracle = new EnhancedHologramOracle(disabledConfig);
      const result = await disabledOracle.validateModule(goodModule);
      
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThanOrEqual(0.95);
      expect(result.execution_time_ms).toBeGreaterThan(0);
      
      // Should still have placeholder data
      expect(result.referenceFingerprint).toBeDefined();
      expect(result.invariantVerifications).toBeDefined();
      expect(result.adaptiveScoring).toBeDefined();
      expect(result.calibrationState).toBeDefined();
    });

    it("updates configuration dynamically", () => {
      const newConfig = {
        calibrationIntervalMs: 5000,
        performanceWindowMs: 10000
      };
      
      oracle.updateConfig(newConfig);
      
      // Configuration should be updated
      const updatedConfig = oracle.getConfig();
      expect(updatedConfig.calibrationIntervalMs).toBe(5000);
      expect(updatedConfig.performanceWindowMs).toBe(10000);
    });
  });

  describe("System Statistics", () => {
    it("provides comprehensive system statistics", () => {
      const stats = oracle.getSystemStats();
      
      expect(stats.referenceFingerprint).toBeDefined();
      expect(stats.invariantVerifier).toBeDefined();
      expect(stats.adaptiveScoring).toBeDefined();
      expect(stats.performanceCalibration).toBeDefined();
      expect(stats.metrics).toBeDefined();
      
      expect(stats.referenceFingerprint.size).toBeGreaterThanOrEqual(0);
      expect(stats.invariantVerifier.size).toBeGreaterThanOrEqual(0);
      expect(stats.adaptiveScoring.size).toBeGreaterThanOrEqual(0);
      expect(stats.performanceCalibration.totalActions).toBeGreaterThanOrEqual(0);
      expect(stats.metrics.counters).toBeDefined();
      expect(stats.metrics.gauges).toBeDefined();
      expect(stats.metrics.hist).toBeDefined();
    });
  });

  describe("Cache Management", () => {
    it("clears all caches", () => {
      oracle.clearCaches();
      
      const stats = oracle.getSystemStats();
      expect(stats.referenceFingerprint.size).toBe(0);
      expect(stats.invariantVerifier.size).toBe(0);
      expect(stats.adaptiveScoring.size).toBe(0);
    });
  });

  describe("Error Handling", () => {
    it("handles missing files gracefully", async () => {
      const result = await oracle.validateModule("nonexistent-file.json");
      
      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBe(0);
      expect(result.violations.length).toBeGreaterThan(0);
      expect(result.violations[0].severity).toBe("critical");
      expect(result.violations[0].message).toContain("Failed to validate module");
    });

    it("handles invalid JSON gracefully", async () => {
      // Create a temporary invalid JSON file
      const fs = require("node:fs");
      const tempFile = "temp-invalid.json";
      fs.writeFileSync(tempFile, "{ invalid json }");
      
      try {
        const result = await oracle.validateModule(tempFile);
        
        expect(result.ok).toBe(false);
        expect(result.oracle_score).toBe(0);
        expect(result.violations.length).toBeGreaterThan(0);
      } finally {
        // Clean up
        fs.unlinkSync(tempFile);
      }
    });
  });

  describe("Performance Characteristics", () => {
    it("executes within reasonable time bounds", async () => {
      const startTime = Date.now();
      const result = await oracle.validateModule(goodModule);
      const executionTime = Date.now() - startTime;
      
      expect(result.execution_time_ms).toBeGreaterThan(0);
      expect(result.execution_time_ms).toBeLessThan(10000); // Should complete within 10 seconds
      expect(executionTime).toBeLessThan(15000); // Total time including overhead
    });

    it("maintains consistent performance across multiple validations", async () => {
      const times: number[] = [];
      
      // Use more samples for better statistical reliability
      for (let i = 0; i < 5; i++) {
        const result = await oracle.validateModule(goodModule);
        times.push(result.execution_time_ms);
      }
      
      // Performance should be relatively consistent
      const avgTime = times.reduce((sum, time) => sum + time, 0) / times.length;
      const maxDeviation = Math.max(...times.map(time => Math.abs(time - avgTime)));
      
      // Use a more reasonable tolerance that accounts for timing variations
      // Allow up to 100% deviation or 2ms, whichever is larger
      const tolerance = Math.max(avgTime * 1.0, 2);
      expect(maxDeviation).toBeLessThan(tolerance);
    });
  });

  describe("Holographic Correspondence", () => {
    it("maintains holographic correspondence across all components", async () => {
      const result = await oracle.validateModule(goodModule);
      
      // All components should have holographic correspondence
      expect(result.holographic_correspondence).toBeTruthy();
      expect(result.referenceFingerprint.digest).toBeTruthy();
      
      result.invariantVerifications.forEach(verification => {
        expect(verification.holographic_correspondence).toBeTruthy();
      });
      
      result.adaptiveScoring.components.forEach(component => {
        expect(component.holographic_correspondence).toBeTruthy();
      });
      
      expect(result.calibrationState.holographic_fingerprint).toBeTruthy();
    });

    it("generates consistent holographic fingerprints", async () => {
      const result1 = await oracle.validateModule(goodModule);
      const result2 = await oracle.validateModule(goodModule);
      
      // Holographic fingerprints should be consistent for the same input
      expect(result1.holographic_fingerprint).toBe(result2.holographic_fingerprint);
      expect(result1.holographic_correspondence).toStrictEqual(result2.holographic_correspondence);
    });
  });

  describe("Integration with Base Oracle", () => {
    it("maintains compatibility with base oracle results", async () => {
      const result = await oracle.validateModule(goodModule);
      
      // Enhanced result should include all base oracle fields
      expect(result.ok).toBeDefined();
      expect(result.oracle_score).toBeDefined();
      expect(result.violations).toBeInstanceOf(Array);
      expect(result.holographic_fingerprint).toBeTruthy();
      
      // Should maintain the same validation logic
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThanOrEqual(0.95);
    });
  });
});

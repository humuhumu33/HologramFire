import { describe, it, expect, beforeEach } from "vitest";
import { MasterHologramOracle, OracleMode } from "../src/validator/MasterHologramOracle";
import { Metrics } from "../src/monitoring/metrics/Metrics";

describe("MasterHologramOracle", () => {
  let oracle: MasterHologramOracle;
  let metrics: Metrics;

  beforeEach(() => {
    metrics = new Metrics();
  });

  describe("Base Mode", () => {
    beforeEach(() => {
      const mode: OracleMode = { 
        type: 'base', 
        config: { 
          threshold: 0.95,
          enableAdaptiveScoring: false,
          enablePerformanceCalibration: false,
          enableMLOptimization: false
        } 
      };
      oracle = new MasterHologramOracle(mode);
    });

    it("should validate a module with basic holographic validation", async () => {
      const moduleData = {
        invariants: ["holographic_correspondence", "resonance_classification", "cycle_conservation", "page_conservation"],
        implementation: {
          native: "test implementation"
        }
      };

      const result = await oracle.validate(moduleData);

      expect(result).toBeDefined();
      expect(result.mode).toBe('base');
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThan(0.9);
      expect(result.violations).toHaveLength(0);
      expect(result.holographic_fingerprint).toBeDefined();
      expect(result.execution_time_ms).toBeGreaterThan(0);
      expect(result.timestamp).toBeGreaterThan(0);
    });

    it("should detect missing holographic correspondence", async () => {
      const moduleData = {
        invariants: ["resonance_classification", "cycle_conservation", "page_conservation"],
        implementation: {
          native: "test implementation"
        }
      };

      const result = await oracle.validate(moduleData);

      expect(result.ok).toBe(false);
      expect(result.violations.length).toBeGreaterThan(0);
      expect(result.violations.some(v => v.type === 'holographic_correspondence')).toBe(true);
    });

    it("should handle missing invariants array", async () => {
      const moduleData = {
        implementation: {
          native: "test implementation"
        }
      };

      const result = await oracle.validate(moduleData);

      expect(result.ok).toBe(false);
      expect(result.violations.length).toBeGreaterThan(0);
      expect(result.violations.some(v => v.type === 'holographic_correspondence')).toBe(true);
    });
  });

  describe("Enhanced Mode", () => {
    beforeEach(() => {
      const mode: OracleMode = { 
        type: 'enhanced', 
        config: { 
          threshold: 0.95,
          enableAdaptiveScoring: true,
          enablePerformanceCalibration: true,
          enableInvariantVerification: true
        } 
      };
      oracle = new MasterHologramOracle(mode);
    });

    it("should provide enhanced validation with adaptive scoring", async () => {
      const moduleData = {
        invariants: ["holographic_correspondence", "resonance_classification", "cycle_conservation", "page_conservation"],
        implementation: {
          native: "test implementation"
        }
      };

      const result = await oracle.validate(moduleData);

      expect(result.mode).toBe('enhanced');
      expect(result.adaptiveScoring).toBeDefined();
      expect(result.invariantVerifications).toBeDefined();
      expect(result.calibrationState).toBeDefined();
    });
  });

  describe("ML-Enhanced Mode", () => {
    beforeEach(() => {
      const mode: OracleMode = { 
        type: 'ml-enhanced', 
        config: { 
          threshold: 0.95,
          enableMLOptimization: true,
          enableMLPerformancePrediction: true,
          enableMLAnomalyDetection: true,
          enableMLPatternRecognition: true
        } 
      };
      oracle = new MasterHologramOracle(mode);
    });

    it("should provide ML-enhanced validation", async () => {
      const moduleData = {
        invariants: ["holographic_correspondence", "resonance_classification", "cycle_conservation", "page_conservation"],
        implementation: {
          native: "test implementation"
        }
      };

      const result = await oracle.validate(moduleData);

      expect(result.mode).toBe('ml-enhanced');
      expect(result.mlConfidence).toBeDefined();
      expect(result.mlRecommendations).toBeDefined();
    });
  });

  describe("Development Mode", () => {
    beforeEach(() => {
      const mode: OracleMode = { 
        type: 'development', 
        config: { 
          threshold: 0.95,
          enableRealTimeFeedback: true,
          enableValidationCache: true
        } 
      };
      oracle = new MasterHologramOracle(mode);
    });

    it("should provide development-focused validation with suggestions", async () => {
      const moduleData = {
        invariants: ["resonance_classification", "cycle_conservation", "page_conservation"], // Missing holographic_correspondence
        implementation: {
          native: "test implementation"
        }
      };

      const result = await oracle.validate(moduleData);

      expect(result.mode).toBe('development');
      expect(result.suggestions).toBeDefined();
      expect(result.quickFixes).toBeDefined();
    });
  });

  describe("Configuration", () => {
    it("should allow configuration updates", () => {
      const mode: OracleMode = { type: 'base', config: {} };
      oracle = new MasterHologramOracle(mode);

      oracle.updateConfig({ threshold: 0.8 });
      const config = oracle.getConfig();
      expect(config.threshold).toBe(0.8);
    });

    it("should allow mode changes", () => {
      const mode: OracleMode = { type: 'base', config: {} };
      oracle = new MasterHologramOracle(mode);

      const newMode: OracleMode = { type: 'enhanced', config: { enableAdaptiveScoring: true } };
      oracle.setMode(newMode);
      
      expect(oracle.getMode().type).toBe('enhanced');
    });
  });

  describe("Statistics", () => {
    it("should provide statistics", () => {
      const mode: OracleMode = { type: 'base', config: {} };
      oracle = new MasterHologramOracle(mode);

      const stats = oracle.getStats();
      expect(stats).toBeDefined();
      expect(stats.mode).toBe('base');
      expect(stats.config).toBeDefined();
    });
  });

  describe("Cache Management", () => {
    it("should clear cache", () => {
      const mode: OracleMode = { type: 'base', config: {} };
      oracle = new MasterHologramOracle(mode);

      // Should not throw
      expect(() => oracle.clearCache()).not.toThrow();
    });
  });

  describe("Error Handling", () => {
    it("should handle validation errors gracefully", async () => {
      const mode: OracleMode = { type: 'base', config: {} };
      oracle = new MasterHologramOracle(mode);

      // Test with invalid input
      const result = await oracle.validate(null);

      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBe(0);
      expect(result.violations.length).toBeGreaterThan(0);
      expect(result.violations[0].severity).toBe('critical');
    });
  });
});

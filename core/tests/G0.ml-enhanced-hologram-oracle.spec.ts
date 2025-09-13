import { describe, it, expect, beforeEach, afterEach, vi } from "vitest";
import { MLEnhancedHologramOracle, MLEnhancedOracleConfig } from "../src/validator/MLEnhancedHologramOracle";
import { MLOracleOptimization } from "../src/validator/MLOracleOptimization";
import { AdaptiveScoringResult, ScoringComponent } from "../src/validator/AdaptiveOracleScoring";
import { InvariantVerificationResult } from "../src/validator/InvariantVerifier";
import { PerformanceSnapshot } from "../src/validator/PerformanceCalibration";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import fs from "node:fs";
import path from "node:path";

describe("ML-Enhanced Hologram Oracle", () => {
  let oracle: MLEnhancedHologramOracle;
  let config: MLEnhancedOracleConfig;
  let mockModuleData: any;

  beforeEach(() => {
    config = {
      enableMLOptimization: true,
      enableMLPerformancePrediction: true,
      enableMLAnomalyDetection: true,
      enableMLPatternRecognition: true,
      mlTrainingIntervalMs: 1000,
      mlPredictionThreshold: 0.8,
      mlAnomalyThreshold: 0.7,
      threshold: 0.95,
      maxViolations: 10,
      calibrationIntervalMs: 5000,
      performanceWindowMs: 10000,
      referenceFingerprintPath: "hologram_generator_mini.py",
      enableDynamicFingerprinting: false,
      enableInvariantVerification: false,
      enableAdaptiveScoring: false,
      enablePerformanceCalibration: false
    };

    oracle = new MLEnhancedHologramOracle(config);

    mockModuleData = {
      name: "test-module",
      invariants: [
        "holographic_correspondence",
        "resonance_classification",
        "cycle_conservation",
        "page_conservation"
      ],
      implementation: {
        holographic: true,
        resonance: true,
        cycle: true,
        page: true
      },
      exports: ["validate", "process", "optimize"]
    };

    // Create temporary test module file
    const testModulePath = "test-module.json";
    fs.writeFileSync(testModulePath, JSON.stringify(mockModuleData, null, 2));
  });

  afterEach(() => {
    oracle.destroy();
    
    // Clean up test files
    const testModulePath = "test-module.json";
    if (fs.existsSync(testModulePath)) {
      fs.unlinkSync(testModulePath);
    }
  });

  describe("ML-Enhanced Module Validation", () => {
    it("should validate module with ML optimization", async () => {
      const result = await oracle.validateModule("test-module.json");

      expect(result).toBeDefined();
      expect(result.ok).toBeDefined();
      expect(result.oracle_score).toBeGreaterThanOrEqual(0);
      expect(result.oracle_score).toBeLessThanOrEqual(1);
      expect(result.mlConfidence).toBeGreaterThanOrEqual(0);
      expect(result.mlConfidence).toBeLessThanOrEqual(1);
      expect(result.mlRecommendations).toBeInstanceOf(Array);
      expect(result.holographic_correspondence).toBeDefined();
    });

    it("should include ML optimization results", async () => {
      const result = await oracle.validateModule("test-module.json");

      if (result.mlOptimization) {
        expect(result.mlOptimization.optimizedWeights).toBeInstanceOf(Map);
        expect(result.mlOptimization.optimizedThresholds).toBeInstanceOf(Map);
        expect(result.mlOptimization.performanceGains).toBeDefined();
        expect(result.mlOptimization.recommendations).toBeInstanceOf(Array);
        expect(result.mlOptimization.holographic_correspondence).toBeDefined();
      }
    });

    it("should include ML performance prediction", async () => {
      const result = await oracle.validateModule("test-module.json");

      if (result.mlPerformancePrediction) {
        expect(result.mlPerformancePrediction.predictions).toBeInstanceOf(Array);
        expect(result.mlPerformancePrediction.confidence).toBeGreaterThanOrEqual(0);
        expect(result.mlPerformancePrediction.confidence).toBeLessThanOrEqual(1);
        expect(result.mlPerformancePrediction.modelVersion).toBeDefined();
        expect(result.mlPerformancePrediction.holographic_fingerprint).toBeDefined();
      }
    });

    it("should include ML anomaly detection", async () => {
      const result = await oracle.validateModule("test-module.json");

      if (result.mlAnomalyDetection) {
        expect(typeof result.mlAnomalyDetection.isAnomaly).toBe("boolean");
        expect(result.mlAnomalyDetection.anomalyScore).toBeGreaterThanOrEqual(0);
        expect(result.mlAnomalyDetection.anomalyScore).toBeLessThanOrEqual(1);
        expect(result.mlAnomalyDetection.anomalyType).toBeDefined();
        expect(result.mlAnomalyDetection.confidence).toBeGreaterThanOrEqual(0);
        expect(result.mlAnomalyDetection.confidence).toBeLessThanOrEqual(1);
        expect(result.mlAnomalyDetection.explanation).toBeDefined();
        expect(result.mlAnomalyDetection.holographic_fingerprint).toBeDefined();
      }
    });

    it("should include ML holographic pattern recognition", async () => {
      const result = await oracle.validateModule("test-module.json");

      if (result.mlHolographicPatterns) {
        expect(result.mlHolographicPatterns).toBeInstanceOf(Array);
        
        result.mlHolographicPatterns.forEach(pattern => {
          expect(pattern.patternType).toBeDefined();
          expect(pattern.strength).toBeGreaterThanOrEqual(0);
          expect(pattern.strength).toBeLessThanOrEqual(1);
          expect(pattern.confidence).toBeGreaterThanOrEqual(0);
          expect(pattern.confidence).toBeLessThanOrEqual(1);
          expect(pattern.features).toBeInstanceOf(Array);
          expect(pattern.explanation).toBeDefined();
          expect(pattern.holographic_fingerprint).toBeDefined();
        });
      }
    });
  });

  describe("ML-Enhanced Blueprint Validation", () => {
    it("should validate blueprint with ML optimization", async () => {
      const result = await oracle.validateBlueprint("test-module.json");

      expect(result).toBeDefined();
      expect(result.ok).toBeDefined();
      expect(result.oracle_score).toBeGreaterThanOrEqual(0);
      expect(result.oracle_score).toBeLessThanOrEqual(1);
      expect(result.mlConfidence).toBeGreaterThanOrEqual(0);
      expect(result.mlConfidence).toBeLessThanOrEqual(1);
      expect(result.mlRecommendations).toBeInstanceOf(Array);
      expect(result.holographic_correspondence).toBeDefined();
    });
  });

  describe("ML Configuration", () => {
    it("should respect ML configuration options", () => {
      const configWithMLDisabled: MLEnhancedOracleConfig = {
        ...config,
        enableMLOptimization: false,
        enableMLPerformancePrediction: false,
        enableMLAnomalyDetection: false,
        enableMLPatternRecognition: false
      };

      const oracleWithMLDisabled = new MLEnhancedHologramOracle(configWithMLDisabled);
      
      expect(oracleWithMLDisabled).toBeDefined();
      
      oracleWithMLDisabled.destroy();
    });

    it("should update ML configuration", () => {
      const newConfig = {
        mlTrainingIntervalMs: 2000,
        mlPredictionThreshold: 0.9,
        mlAnomalyThreshold: 0.8
      };

      oracle.updateMLConfig(newConfig);
      
      const stats = oracle.getMLStats();
      expect(stats.mlConfig.mlTrainingIntervalMs).toBe(2000);
      expect(stats.mlConfig.mlPredictionThreshold).toBe(0.9);
      expect(stats.mlConfig.mlAnomalyThreshold).toBe(0.8);
    });
  });

  describe("ML Statistics", () => {
    it("should provide ML statistics", () => {
      const stats = oracle.getMLStats();

      expect(stats).toBeDefined();
      expect(stats.mlConfig).toBeDefined();
      expect(stats.mlModelStats).toBeDefined();
      expect(stats.performanceHistorySize).toBeGreaterThanOrEqual(0);
      expect(typeof stats.mlTrainingActive).toBe("boolean");
    });

    it("should provide system statistics", () => {
      const stats = oracle.getSystemStats();

      expect(stats).toBeDefined();
      expect(stats.metrics).toBeDefined();
    });
  });

  describe("ML Data Management", () => {
    it("should clear ML data", () => {
      oracle.clearMLData();
      
      const stats = oracle.getMLStats();
      expect(stats.performanceHistorySize).toBe(0);
    });
  });

  describe("Error Handling", () => {
    it("should handle ML optimization failures gracefully", async () => {
      // Mock ML optimization to throw error
      const originalOptimizeOracleScoring = oracle["mlOptimization"].optimizeOracleScoring;
      oracle["mlOptimization"].optimizeOracleScoring = vi.fn().mockRejectedValue(new Error("ML optimization failed"));

      const result = await oracle.validateModule("test-module.json");

      expect(result).toBeDefined();
      expect(result.ok).toBeDefined();
      expect(result.mlConfidence).toBe(0);
      expect(result.mlRecommendations.length).toBeGreaterThan(0);
      expect(result.mlRecommendations.some(rec => rec.includes("ML optimization failed"))).toBe(true);

      // Restore original method
      oracle["mlOptimization"].optimizeOracleScoring = originalOptimizeOracleScoring;
    });

    it("should handle missing module file", async () => {
      const result = await oracle.validateModule("nonexistent-module.json");

      expect(result).toBeDefined();
      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBe(0);
    });
  });
});

describe("ML Oracle Optimization", () => {
  let mlOptimization: MLOracleOptimization;
  let mockScoringComponents: ScoringComponent[];
  let mockEnvironmentalFactors: any;
  let mockHistoricalData: any;

  beforeEach(() => {
    mlOptimization = new MLOracleOptimization();

    mockScoringComponents = [
      {
        name: "holographic_correspondence",
        weight: 0.25,
        score: 0.9,
        history: [0.85, 0.88, 0.9],
        trend: "improving" as const
      },
      {
        name: "resonance_classification",
        weight: 0.15,
        score: 0.7,
        history: [0.65, 0.68, 0.7],
        trend: "improving" as const
      }
    ];

    mockEnvironmentalFactors = {
      systemLoad: 0.5,
      memoryPressure: 0.3,
      networkLatency: 10,
      cpuUtilization: 0.4,
      energyEfficiency: 0.8
    };

    mockHistoricalData = {
      averageScores: new Map([["holographic_correspondence", 0.85]]),
      scoreVariance: new Map([["holographic_correspondence", 0.1]]),
      trendDirection: new Map([["holographic_correspondence", "stable"]]),
      lastUpdated: new Date().toISOString()
    };
  });

  afterEach(() => {
    mlOptimization.clearMLData();
  });

  describe("Oracle Scoring Optimization", () => {
    it("should optimize oracle scoring", async () => {
      const result = await mlOptimization.optimizeOracleScoring(
        mockScoringComponents,
        mockEnvironmentalFactors,
        mockHistoricalData
      );

      expect(result).toBeDefined();
      expect(result.optimizedWeights).toBeInstanceOf(Map);
      expect(result.optimizedThresholds).toBeInstanceOf(Map);
      expect(result.performanceGains).toBeDefined();
      expect(result.recommendations).toBeInstanceOf(Array);
      expect(result.holographic_correspondence).toBeDefined();
    });

    it("should provide performance gains", async () => {
      const result = await mlOptimization.optimizeOracleScoring(
        mockScoringComponents,
        mockEnvironmentalFactors,
        mockHistoricalData
      );

      expect(result.performanceGains.accuracy).toBeGreaterThanOrEqual(0);
      expect(result.performanceGains.speed).toBeGreaterThanOrEqual(0);
      expect(result.performanceGains.energy).toBeGreaterThanOrEqual(0);
      expect(result.performanceGains.stability).toBeGreaterThanOrEqual(0);
    });
  });

  describe("Performance Prediction", () => {
    it("should predict oracle performance", async () => {
      const mockModuleData = { name: "test", invariants: ["test"] };
      const mockMetrics = new Metrics();

      const result = await mlOptimization.predictOraclePerformance(
        mockModuleData,
        mockEnvironmentalFactors,
        mockMetrics
      );

      expect(result).toBeDefined();
      expect(result.predictions).toBeInstanceOf(Array);
      expect(result.confidence).toBeGreaterThanOrEqual(0);
      expect(result.confidence).toBeLessThanOrEqual(1);
      expect(result.modelVersion).toBeDefined();
      expect(result.holographic_fingerprint).toBeDefined();
    });
  });

  describe("Anomaly Detection", () => {
    it("should detect anomalies", async () => {
      const mockCurrentSnapshot: PerformanceSnapshot = {
        timestamp: new Date().toISOString(),
        metrics: { responseTime: 0, throughput: 0, accuracy: 0, stability: 0 },
        systemLoad: 0.5,
        memoryUsage: 512,
        energyEfficiency: 0.3, // Low energy efficiency
        environmentalFactors: mockEnvironmentalFactors,
        oracleScore: 0.5, // Low score to trigger anomaly
        executionTime: 5000 // High execution time
      };

      const mockHistoricalSnapshots: PerformanceSnapshot[] = [
        {
          timestamp: new Date(Date.now() - 60000).toISOString(),
          metrics: { responseTime: 0, throughput: 0, accuracy: 0, stability: 0 },
          systemLoad: 0.3,
          memoryUsage: 256,
          energyEfficiency: 0.9,
          environmentalFactors: mockEnvironmentalFactors,
          oracleScore: 0.95,
          executionTime: 1000
        }
      ];

      const result = await mlOptimization.detectAnomalies(mockCurrentSnapshot, mockHistoricalSnapshots);

      expect(result).toBeDefined();
      expect(typeof result.isAnomaly).toBe("boolean");
      expect(result.anomalyScore).toBeGreaterThanOrEqual(0);
      expect(result.anomalyScore).toBeLessThanOrEqual(1);
      expect(result.anomalyType).toBeDefined();
      expect(result.confidence).toBeGreaterThanOrEqual(0);
      expect(result.confidence).toBeLessThanOrEqual(1);
      expect(result.explanation).toBeDefined();
      expect(result.holographic_fingerprint).toBeDefined();
    });
  });

  describe("Holographic Pattern Recognition", () => {
    it("should recognize holographic patterns", async () => {
      const mockModuleData = {
        name: "test-module",
        invariants: ["holographic_correspondence", "resonance_classification"],
        implementation: {
          holographic: true,
          resonance: true,
          cycle: true,
          page: true
        }
      };

      const mockVerificationResults: InvariantVerificationResult[] = [
        {
          invariant: "holographic_correspondence",
          verified: true,
          confidence: 0.9,
          evidence: { type: "computational", proof: null, witness: "test", details: "test" },
          holographic_correspondence: "test",
          execution_time_ms: 100
        }
      ];

      const result = await mlOptimization.recognizeHolographicPatterns(
        mockModuleData,
        mockVerificationResults
      );

      expect(result).toBeDefined();
      expect(result).toBeInstanceOf(Array);
      
      result.forEach(pattern => {
        expect(pattern.patternType).toBeDefined();
        expect(pattern.strength).toBeGreaterThanOrEqual(0);
        expect(pattern.strength).toBeLessThanOrEqual(1);
        expect(pattern.confidence).toBeGreaterThanOrEqual(0);
        expect(pattern.confidence).toBeLessThanOrEqual(1);
        expect(pattern.features).toBeInstanceOf(Array);
        expect(pattern.explanation).toBeDefined();
        expect(pattern.holographic_fingerprint).toBeDefined();
      });
    });
  });

  describe("ML Model Training", () => {
    it("should train ML models", async () => {
      const mockTrainingData = {
        features: [
          [0.9, 1000, 0.8, 0.5, 0.3, 0.4, 0.8],
          [0.8, 1200, 0.7, 0.6, 0.4, 0.5, 0.7]
        ],
        targets: [
          [0.9, 1000, 0.8],
          [0.8, 1200, 0.7]
        ],
        metadata: [
          {
            timestamp: new Date().toISOString(),
            modulePath: "test1.json",
            oracleScore: 0.9,
            executionTime: 1000,
            environmentalFactors: mockEnvironmentalFactors
          },
          {
            timestamp: new Date().toISOString(),
            modulePath: "test2.json",
            oracleScore: 0.8,
            executionTime: 1200,
            environmentalFactors: mockEnvironmentalFactors
          }
        ]
      };

      await expect(mlOptimization.trainModels(mockTrainingData)).resolves.not.toThrow();
    });
  });

  describe("ML Model Statistics", () => {
    it("should provide model statistics", () => {
      const stats = mlOptimization.getModelStats();

      expect(stats).toBeDefined();
      expect(stats.models).toBeInstanceOf(Array);
      expect(stats.trainingDataSize).toBeGreaterThanOrEqual(0);
      expect(stats.holographicEmbeddings).toBeGreaterThanOrEqual(0);
    });
  });

  describe("Data Management", () => {
    it("should clear ML data", () => {
      mlOptimization.clearMLData();
      
      const stats = mlOptimization.getModelStats();
      expect(stats.trainingDataSize).toBe(0);
      expect(stats.holographicEmbeddings).toBe(0);
    });
  });
});

describe("ML-Enhanced Oracle Integration", () => {
  it("should integrate with existing oracle system", async () => {
    const config: MLEnhancedOracleConfig = {
      enableMLOptimization: true,
      enableMLPerformancePrediction: true,
      enableMLAnomalyDetection: true,
      enableMLPatternRecognition: true,
      threshold: 0.95,
      maxViolations: 10,
      calibrationIntervalMs: 5000,
      performanceWindowMs: 10000,
      referenceFingerprintPath: "hologram_generator_mini.py",
      enableDynamicFingerprinting: true,
      enableInvariantVerification: true,
      enableAdaptiveScoring: true,
      enablePerformanceCalibration: true
    };

    const oracle = new MLEnhancedHologramOracle(config);
    
    const mockModuleData = {
      name: "integration-test",
      invariants: ["holographic_correspondence"],
      implementation: { holographic: true },
      exports: ["test"]
    };

    const testModulePath = "integration-test.json";
    fs.writeFileSync(testModulePath, JSON.stringify(mockModuleData, null, 2));

    try {
      const result = await oracle.validateModule(testModulePath);

      expect(result).toBeDefined();
      expect(result.ok).toBeDefined();
      expect(result.oracle_score).toBeGreaterThanOrEqual(0);
      expect(result.oracle_score).toBeLessThanOrEqual(1);
      expect(result.mlConfidence).toBeGreaterThanOrEqual(0);
      expect(result.mlConfidence).toBeLessThanOrEqual(1);
      expect(result.mlRecommendations).toBeInstanceOf(Array);
      expect(result.holographic_correspondence).toBeDefined();

      // Check that all ML components are integrated
      expect(result.mlOptimization).toBeDefined();
      expect(result.mlPerformancePrediction).toBeDefined();
      expect(result.mlAnomalyDetection).toBeDefined();
      expect(result.mlHolographicPatterns).toBeDefined();

    } finally {
      oracle.destroy();
      if (fs.existsSync(testModulePath)) {
        fs.unlinkSync(testModulePath);
      }
    }
  });
});

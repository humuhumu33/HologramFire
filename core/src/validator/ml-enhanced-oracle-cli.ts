#!/usr/bin/env node

import { Command } from "commander";
import { MLEnhancedHologramOracle, MLEnhancedOracleConfig } from "./MLEnhancedHologramOracle";
import { MLOracleOptimization } from "./MLOracleOptimization";
import fs from "node:fs";
import path from "node:path";

/**
 * ML-Enhanced Oracle CLI
 * 
 * Command-line interface for the ML-powered hologram oracle optimization system.
 */

const program = new Command();

program
  .name("ml-enhanced-oracle")
  .description("ML-Enhanced Hologram Oracle CLI")
  .version("1.0.0");

// Global options
program
  .option("--verbose", "Enable verbose output")
  .option("--no-ml-optimization", "Disable ML optimization")
  .option("--no-ml-prediction", "Disable ML performance prediction")
  .option("--no-ml-anomaly", "Disable ML anomaly detection")
  .option("--no-ml-patterns", "Disable ML pattern recognition")
  .option("--ml-training-interval <ms>", "ML training interval in milliseconds", "300000")
  .option("--ml-prediction-threshold <score>", "ML prediction confidence threshold", "0.8")
  .option("--ml-anomaly-threshold <score>", "ML anomaly detection threshold", "0.7")
  .option("--python-path <path>", "Python executable path", "python3")
  .option("--hologram-path <path>", "Hologram generator path", "hologram_generator_mini.py");

/**
 * Validate module with ML enhancement
 */
program
  .command("validate-module <modulePath>")
  .description("Validate a module with ML-enhanced oracle")
  .option("--output <file>", "Output results to file")
  .option("--format <format>", "Output format (json, yaml, text)", "json")
  .action(async (modulePath: string, options: any) => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const result = await oracle.validateModule(modulePath);
      
      if (options.output) {
        await writeOutput(result, options.output, options.format);
      } else {
        displayResult(result, options.format, globalOptions.verbose);
      }
      
      // Exit with appropriate code
      process.exit(result.ok ? 0 : 1);
      
    } catch (error) {
      console.error(`Error validating module: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * Validate blueprint with ML enhancement
 */
program
  .command("validate-blueprint <blueprintPath>")
  .description("Validate a blueprint with ML-enhanced oracle")
  .option("--output <file>", "Output results to file")
  .option("--format <format>", "Output format (json, yaml, text)", "json")
  .action(async (blueprintPath: string, options: any) => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const result = await oracle.validateBlueprint(blueprintPath);
      
      if (options.output) {
        await writeOutput(result, options.output, options.format);
      } else {
        displayResult(result, options.format, globalOptions.verbose);
      }
      
      // Exit with appropriate code
      process.exit(result.ok ? 0 : 1);
      
    } catch (error) {
      console.error(`Error validating blueprint: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * Train ML models
 */
program
  .command("train-ml")
  .description("Train ML models with collected data")
  .option("--data-file <file>", "Training data file")
  .option("--epochs <count>", "Number of training epochs", "100")
  .option("--batch-size <size>", "Training batch size", "32")
  .action(async (options: any) => {
    try {
      const mlOptimization = new MLOracleOptimization();
      
      let trainingData;
      if (options.dataFile) {
        trainingData = JSON.parse(fs.readFileSync(options.dataFile, "utf8"));
      } else {
        // Generate sample training data
        trainingData = generateSampleTrainingData();
      }
      
      await mlOptimization.trainModels(trainingData);
      
      console.log("✅ ML models trained successfully");
      console.log(`📊 Training data: ${trainingData.features.length} samples`);
      
    } catch (error) {
      console.error(`Error training ML models: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * ML model statistics
 */
program
  .command("ml-stats")
  .description("Show ML model statistics")
  .action(async () => {
    try {
      const mlOptimization = new MLOracleOptimization();
      const stats = mlOptimization.getModelStats();
      
      console.log("🤖 ML Model Statistics");
      console.log("=====================");
      console.log(`Models: ${stats.models.length}`);
      console.log(`Training Data Size: ${stats.trainingDataSize}`);
      console.log(`Holographic Embeddings: ${stats.holographicEmbeddings}`);
      console.log();
      
      console.log("Model Details:");
      stats.models.forEach((model: any) => {
        console.log(`  ${model.name}:`);
        console.log(`    Type: ${model.type}`);
        console.log(`    Version: ${model.version}`);
        console.log(`    Last Trained: ${model.lastTrained || 'Never'}`);
      });
      
    } catch (error) {
      console.error(`Error getting ML stats: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * ML optimization recommendations
 */
program
  .command("ml-recommendations <modulePath>")
  .description("Get ML optimization recommendations for a module")
  .action(async (modulePath: string) => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const result = await oracle.validateModule(modulePath);
      
      console.log("🎯 ML Optimization Recommendations");
      console.log("==================================");
      console.log(`Module: ${modulePath}`);
      console.log(`ML Confidence: ${(result.mlConfidence * 100).toFixed(1)}%`);
      console.log();
      
      if (result.mlRecommendations.length > 0) {
        console.log("Recommendations:");
        result.mlRecommendations.forEach((rec, index) => {
          console.log(`  ${index + 1}. ${rec}`);
        });
      } else {
        console.log("No specific recommendations at this time.");
      }
      
      if (result.mlOptimization) {
        console.log();
        console.log("Performance Gains:");
        const gains = result.mlOptimization.performanceGains;
        console.log(`  Accuracy: +${(gains.accuracy * 100).toFixed(1)}%`);
        console.log(`  Speed: +${(gains.speed * 100).toFixed(1)}%`);
        console.log(`  Energy: +${(gains.energy * 100).toFixed(1)}%`);
        console.log(`  Stability: +${(gains.stability * 100).toFixed(1)}%`);
      }
      
    } catch (error) {
      console.error(`Error getting ML recommendations: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * Anomaly detection
 */
program
  .command("detect-anomalies <modulePath>")
  .description("Detect anomalies in module validation")
  .action(async (modulePath: string) => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const result = await oracle.validateModule(modulePath);
      
      console.log("🔍 Anomaly Detection Results");
      console.log("============================");
      console.log(`Module: ${modulePath}`);
      
      if (result.mlAnomalyDetection) {
        const anomaly = result.mlAnomalyDetection;
        console.log(`Anomaly Detected: ${anomaly.isAnomaly ? 'YES' : 'NO'}`);
        console.log(`Anomaly Score: ${(anomaly.anomalyScore * 100).toFixed(1)}%`);
        console.log(`Anomaly Type: ${anomaly.anomalyType}`);
        console.log(`Confidence: ${(anomaly.confidence * 100).toFixed(1)}%`);
        console.log(`Explanation: ${anomaly.explanation}`);
      } else {
        console.log("Anomaly detection not available.");
      }
      
    } catch (error) {
      console.error(`Error detecting anomalies: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * Holographic pattern recognition
 */
program
  .command("recognize-patterns <modulePath>")
  .description("Recognize holographic patterns in module")
  .action(async (modulePath: string) => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const result = await oracle.validateModule(modulePath);
      
      console.log("🔮 Holographic Pattern Recognition");
      console.log("==================================");
      console.log(`Module: ${modulePath}`);
      
      if (result.mlHolographicPatterns && result.mlHolographicPatterns.length > 0) {
        console.log(`Patterns Found: ${result.mlHolographicPatterns.length}`);
        console.log();
        
        result.mlHolographicPatterns.forEach((pattern, index) => {
          console.log(`Pattern ${index + 1}:`);
          console.log(`  Type: ${pattern.patternType}`);
          console.log(`  Strength: ${(pattern.strength * 100).toFixed(1)}%`);
          console.log(`  Confidence: ${(pattern.confidence * 100).toFixed(1)}%`);
          console.log(`  Explanation: ${pattern.explanation}`);
          console.log();
        });
      } else {
        console.log("No holographic patterns detected.");
      }
      
    } catch (error) {
      console.error(`Error recognizing patterns: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * Performance prediction
 */
program
  .command("predict-performance <modulePath>")
  .description("Predict oracle performance for module")
  .action(async (modulePath: string) => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const result = await oracle.validateModule(modulePath);
      
      console.log("📊 Performance Prediction");
      console.log("=========================");
      console.log(`Module: ${modulePath}`);
      
      if (result.mlPerformancePrediction) {
        const prediction = result.mlPerformancePrediction;
        console.log(`Confidence: ${(prediction.confidence * 100).toFixed(1)}%`);
        console.log(`Model Version: ${prediction.modelVersion}`);
        console.log();
        
        if (prediction.predictions.length >= 3) {
          console.log("Predicted Metrics:");
          console.log(`  Oracle Score: ${(prediction.predictions[0] * 100).toFixed(1)}%`);
          console.log(`  Execution Time: ${prediction.predictions[1].toFixed(0)}ms`);
          console.log(`  Energy Efficiency: ${(prediction.predictions[2] * 100).toFixed(1)}%`);
        }
      } else {
        console.log("Performance prediction not available.");
      }
      
    } catch (error) {
      console.error(`Error predicting performance: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * System statistics
 */
program
  .command("system-stats")
  .description("Show ML-enhanced oracle system statistics")
  .action(async () => {
    try {
      const globalOptions = program.opts();
      const config = createMLConfig(globalOptions);
      
      const oracle = new MLEnhancedHologramOracle(config);
      const stats = oracle.getSystemStats();
      const mlStats = oracle.getMLStats();
      
      console.log("📈 ML-Enhanced Oracle System Statistics");
      console.log("=======================================");
      console.log();
      
      console.log("Base Oracle Stats:");
      console.log(`  Reference Fingerprint: ${stats.referenceFingerprint?.hitRate || 0}% hit rate`);
      console.log(`  Invariant Verifier: ${stats.invariantVerifier?.hitRate || 0}% hit rate`);
      console.log(`  Adaptive Scoring: ${stats.adaptiveScoring?.hitRate || 0}% hit rate`);
      console.log(`  Performance Calibration: ${stats.performanceCalibration?.totalActions || 0} actions`);
      console.log();
      
      console.log("ML Enhancement Stats:");
      console.log(`  ML Optimization: ${mlStats.mlConfig.enableMLOptimization ? 'Enabled' : 'Disabled'}`);
      console.log(`  ML Prediction: ${mlStats.mlConfig.enableMLPerformancePrediction ? 'Enabled' : 'Disabled'}`);
      console.log(`  ML Anomaly Detection: ${mlStats.mlConfig.enableMLAnomalyDetection ? 'Enabled' : 'Disabled'}`);
      console.log(`  ML Pattern Recognition: ${mlStats.mlConfig.enableMLPatternRecognition ? 'Enabled' : 'Disabled'}`);
      console.log(`  Performance History: ${mlStats.performanceHistorySize} snapshots`);
      console.log(`  ML Training Active: ${mlStats.mlTrainingActive ? 'Yes' : 'No'}`);
      console.log();
      
      console.log("ML Model Stats:");
      mlStats.mlModelStats.models.forEach((model: any) => {
        console.log(`  ${model.name}: v${model.version} (${model.type})`);
      });
      
    } catch (error) {
      console.error(`Error getting system stats: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  });

/**
 * Creates ML configuration from CLI options
 */
function createMLConfig(options: any): MLEnhancedOracleConfig {
  return {
    enableMLOptimization: options.mlOptimization !== false,
    enableMLPerformancePrediction: options.mlPrediction !== false,
    enableMLAnomalyDetection: options.mlAnomaly !== false,
    enableMLPatternRecognition: options.mlPatterns !== false,
    mlTrainingIntervalMs: parseInt(options.mlTrainingInterval),
    mlPredictionThreshold: parseFloat(options.mlPredictionThreshold),
    mlAnomalyThreshold: parseFloat(options.mlAnomalyThreshold),
    threshold: 0.95,
    maxViolations: 10,
    calibrationIntervalMs: 5000,
    performanceWindowMs: 10000,
    referenceFingerprintPath: options.hologramPath,
    enableDynamicFingerprinting: true,
    enableInvariantVerification: true,
    enableAdaptiveScoring: true,
    enablePerformanceCalibration: true
  };
}

/**
 * Displays result in specified format
 */
function displayResult(result: any, format: string, verbose: boolean): void {
  switch (format.toLowerCase()) {
    case "json":
      console.log(JSON.stringify(result, null, 2));
      break;
    case "yaml":
      console.log(JSON.stringify(result, null, 2)); // Simplified YAML output
      break;
    case "text":
      displayTextResult(result, verbose);
      break;
    default:
      console.log(JSON.stringify(result, null, 2));
  }
}

/**
 * Displays result in text format
 */
function displayTextResult(result: any, verbose: boolean): void {
  console.log("🔮 ML-Enhanced Oracle Validation Result");
  console.log("======================================");
  console.log(`Status: ${result.ok ? '✅ PASS' : '❌ FAIL'}`);
  console.log(`Oracle Score: ${(result.oracle_score * 100).toFixed(1)}%`);
  console.log(`Execution Time: ${result.execution_time_ms}ms`);
  console.log(`ML Confidence: ${(result.mlConfidence * 100).toFixed(1)}%`);
  console.log();
  
  if (result.violations.length > 0) {
    console.log("Violations:");
    result.violations.forEach((violation: any, index: number) => {
      console.log(`  ${index + 1}. [${violation.severity.toUpperCase()}] ${violation.message}`);
    });
    console.log();
  }
  
  if (result.mlRecommendations.length > 0) {
    console.log("ML Recommendations:");
    result.mlRecommendations.forEach((rec: string, index: number) => {
      console.log(`  ${index + 1}. ${rec}`);
    });
    console.log();
  }
  
  if (verbose) {
    if (result.mlOptimization) {
      console.log("ML Optimization:");
      const gains = result.mlOptimization.performanceGains;
      console.log(`  Accuracy Gain: +${(gains.accuracy * 100).toFixed(1)}%`);
      console.log(`  Speed Gain: +${(gains.speed * 100).toFixed(1)}%`);
      console.log(`  Energy Gain: +${(gains.energy * 100).toFixed(1)}%`);
      console.log(`  Stability Gain: +${(gains.stability * 100).toFixed(1)}%`);
      console.log();
    }
    
    if (result.mlAnomalyDetection) {
      console.log("Anomaly Detection:");
      const anomaly = result.mlAnomalyDetection;
      console.log(`  Anomaly: ${anomaly.isAnomaly ? 'YES' : 'NO'}`);
      console.log(`  Score: ${(anomaly.anomalyScore * 100).toFixed(1)}%`);
      console.log(`  Type: ${anomaly.anomalyType}`);
      console.log();
    }
    
    if (result.mlHolographicPatterns && result.mlHolographicPatterns.length > 0) {
      console.log("Holographic Patterns:");
      result.mlHolographicPatterns.forEach((pattern: any, index: number) => {
        console.log(`  ${index + 1}. ${pattern.patternType} (${(pattern.strength * 100).toFixed(1)}%)`);
      });
      console.log();
    }
  }
}

/**
 * Writes output to file
 */
async function writeOutput(result: any, outputPath: string, format: string): Promise<void> {
  let content: string;
  
  switch (format.toLowerCase()) {
    case "json":
      content = JSON.stringify(result, null, 2);
      break;
    case "yaml":
      content = JSON.stringify(result, null, 2); // Simplified YAML output
      break;
    case "text":
      content = JSON.stringify(result, null, 2); // Simplified text output
      break;
    default:
      content = JSON.stringify(result, null, 2);
  }
  
  fs.writeFileSync(outputPath, content, "utf8");
  console.log(`✅ Results written to ${outputPath}`);
}

/**
 * Generates sample training data
 */
function generateSampleTrainingData(): any {
  const features: number[][] = [];
  const targets: number[][] = [];
  const metadata: any[] = [];
  
  // Generate 100 sample training examples
  for (let i = 0; i < 100; i++) {
    const featureVector = [
      Math.random(), // oracle score
      Math.random() * 2000, // execution time
      Math.random(), // energy efficiency
      Math.random(), // system load
      Math.random(), // memory pressure
      Math.random(), // cpu utilization
      Math.random() // energy efficiency
    ];
    
    const targetVector = [
      Math.random(), // target oracle score
      Math.random() * 2000, // target execution time
      Math.random() // target energy efficiency
    ];
    
    features.push(featureVector);
    targets.push(targetVector);
    metadata.push({
      timestamp: new Date().toISOString(),
      modulePath: `sample-module-${i}.json`,
      oracleScore: featureVector[0],
      executionTime: featureVector[1],
      environmentalFactors: {
        systemLoad: featureVector[3],
        memoryPressure: featureVector[4],
        cpuUtilization: featureVector[5],
        energyEfficiency: featureVector[6],
        networkLatency: 0
      }
    });
  }
  
  return { features, targets, metadata };
}

// Parse command line arguments
program.parse();

#!/usr/bin/env ts-node

/**
 * Enhanced Oracle Demonstration Script
 * 
 * Demonstrates the four high-priority improvements:
 * 1. Dynamic reference fingerprinting from hologram_generator_mini.py
 * 2. Actual invariant verification beyond presence checking
 * 3. Adaptive oracle scoring with weighted components
 * 4. Real-time performance calibration feedback loops
 */

import { EnhancedHologramOracle, EnhancedOracleConfig } from "../../src/validator/EnhancedHologramOracle";
import { DynamicReferenceFingerprint } from "../../src/validator/ReferenceFingerprint";
import { InvariantVerifier } from "../../src/validator/InvariantVerifier";
import { AdaptiveOracleScoring } from "../../src/validator/AdaptiveOracleScoring";
import { PerformanceCalibration } from "../../src/validator/PerformanceCalibration";
import { Metrics } from "../../src/monitoring/metrics/Metrics";
import path from "node:path";

async function demonstrateEnhancedOracle() {
  console.log("🚀 Enhanced Hologram Oracle Demonstration");
  console.log("==========================================\n");

  // Configuration
  const config: EnhancedOracleConfig = {
    enableDynamicFingerprinting: true,
    enableInvariantVerification: true,
    enableAdaptiveScoring: true,
    enablePerformanceCalibration: true,
    enableMLOptimization: false,
    threshold: 0.95,
    maxViolations: 5,
    referenceFingerprintPath: "hologram_generator_mini.py",
    calibrationIntervalMs: 5000, // 5 seconds for demo
    performanceWindowMs: 30000   // 30 seconds for demo
  };

  console.log("📊 Configuration:");
  console.log(`  Dynamic Fingerprinting: ${config.enableDynamicFingerprinting ? "✅" : "❌"}`);
  console.log(`  Invariant Verification: ${config.enableInvariantVerification ? "✅" : "❌"}`);
  console.log(`  Adaptive Scoring: ${config.enableAdaptiveScoring ? "✅" : "❌"}`);
  console.log(`  Performance Calibration: ${config.enablePerformanceCalibration ? "✅" : "❌"}`);
  console.log(`  Reference Path: ${config.referenceFingerprintPath}`);
  console.log(`  Calibration Interval: ${config.calibrationIntervalMs}ms`);
  console.log(`  Performance Window: ${config.performanceWindowMs}ms\n`);

  // Initialize enhanced oracle
  console.log("🔧 Initializing Enhanced Oracle...");
  const oracle = new EnhancedHologramOracle(config);
  console.log("✅ Enhanced Oracle initialized\n");

  // Test modules
  const testModules = [
    "modules/example-good.json",
    "modules/example-bad.json"
  ];

  for (const modulePath of testModules) {
    console.log(`🔍 Validating Module: ${modulePath}`);
    console.log("─".repeat(50));

    try {
      const startTime = Date.now();
      const result = await oracle.validateModule(modulePath);
      const totalTime = Date.now() - startTime;

      // Display results
      console.log(`📋 Validation Results:`);
      console.log(`  Status: ${result.ok ? "✅ PASS" : "❌ FAIL"}`);
      console.log(`  Oracle Score: ${result.oracle_score.toFixed(4)}`);
      console.log(`  Execution Time: ${result.execution_time_ms}ms`);
      console.log(`  Total Time: ${totalTime}ms`);
      console.log(`  Violations: ${result.violations.length}`);

      if (result.violations.length > 0) {
        console.log(`  Violation Details:`);
        result.violations.forEach((violation: any, index: number) => {
          console.log(`    ${index + 1}. [${violation.severity.toUpperCase()}] ${violation.type}: ${violation.message}`);
        });
      }

      // Reference Fingerprinting
      if (config.enableDynamicFingerprinting) {
        console.log(`\n🔗 Reference Fingerprinting:`);
        console.log(`  Version: ${result.referenceFingerprint.version}`);
        console.log(`  Python Hash: ${result.referenceFingerprint.python_hash.substring(0, 16)}...`);
        console.log(`  Execution Witness: ${result.referenceFingerprint.execution_witness.substring(0, 16)}...`);
        console.log(`  Holographic Correspondence: ${result.referenceFingerprint.holographic_correspondence.substring(0, 16)}...`);
        console.log(`  Digest: ${result.referenceFingerprint.digest.substring(0, 16)}...`);
        console.log(`  Timestamp: ${result.referenceFingerprint.timestamp}`);
      }

      // Invariant Verification
      if (config.enableInvariantVerification) {
        console.log(`\n🧪 Invariant Verification:`);
        console.log(`  Total Verifications: ${result.invariantVerifications.length}`);
        
        const verifiedCount = result.invariantVerifications.filter((v: any) => v.verified).length;
        const avgConfidence = result.invariantVerifications.reduce((sum: number, v: any) => sum + v.confidence, 0) / 
                             Math.max(1, result.invariantVerifications.length);
        
        console.log(`  Verified: ${verifiedCount}/${result.invariantVerifications.length}`);
        console.log(`  Average Confidence: ${avgConfidence.toFixed(3)}`);
        
        if (result.invariantVerifications.length > 0) {
          console.log(`  Verification Details:`);
          result.invariantVerifications.forEach((verification: any, index: number) => {
            const status = verification.verified ? "✅" : "❌";
            console.log(`    ${index + 1}. ${status} ${verification.invariant}: ${verification.confidence.toFixed(3)} confidence`);
          });
        }
      }

      // Adaptive Scoring
      if (config.enableAdaptiveScoring) {
        console.log(`\n📈 Adaptive Scoring:`);
        console.log(`  Overall Score: ${result.adaptiveScoring.overallScore.toFixed(4)}`);
        console.log(`  Threshold: ${result.adaptiveScoring.threshold.toFixed(4)}`);
        console.log(`  Confidence: ${result.adaptiveScoring.confidence.toFixed(3)}`);
        console.log(`  Recommendation: ${result.adaptiveScoring.recommendation}`);
        
        if (result.adaptiveScoring.components.length > 0) {
          console.log(`  Component Scores:`);
          result.adaptiveScoring.components.forEach((component: any, index: number) => {
            console.log(`    ${index + 1}. ${component.name}: ${component.score.toFixed(3)} (weight: ${component.weight.toFixed(3)})`);
          });
        }

        console.log(`  Adaptive Factors:`);
        console.log(`    Load Adjustment: ${result.adaptiveScoring.adaptive_factors.loadAdjustment.toFixed(3)}`);
        console.log(`    Performance Adjustment: ${result.adaptiveScoring.adaptive_factors.performanceAdjustment.toFixed(3)}`);
        console.log(`    Historical Adjustment: ${result.adaptiveScoring.adaptive_factors.historicalAdjustment.toFixed(3)}`);
        console.log(`    Environmental Adjustment: ${result.adaptiveScoring.adaptive_factors.environmentalAdjustment.toFixed(3)}`);
        console.log(`    Confidence Adjustment: ${result.adaptiveScoring.adaptive_factors.confidenceAdjustment.toFixed(3)}`);
      }

      // Performance Calibration
      if (config.enablePerformanceCalibration) {
        console.log(`\n🎛️  Performance Calibration:`);
        console.log(`  Active Targets: ${result.calibrationState.targets.size}`);
        console.log(`  Total Actions: ${result.calibrationState.actions.length}`);
        console.log(`  Feedback Entries: ${result.calibrationState.feedback.length}`);
        console.log(`  Performance History: ${result.calibrationState.performanceHistory.length} snapshots`);
        console.log(`  Last Calibration: ${result.calibrationState.lastCalibration}`);
        
        if (result.calibrationState.actions.length > 0) {
          console.log(`  Recent Actions:`);
          result.calibrationState.actions.slice(-3).forEach((action: any, index: number) => {
            console.log(`    ${index + 1}. ${action.type}: ${action.target} (magnitude: ${action.magnitude.toFixed(3)})`);
          });
        }
      }

      // Holographic Correspondence
      console.log(`\n🔮 Holographic Correspondence:`);
      console.log(`  Module Fingerprint: ${result.holographic_fingerprint.substring(0, 16)}...`);
      console.log(`  Correspondence Hash: ${result.holographic_correspondence.substring(0, 16)}...`);

    } catch (error) {
      console.log(`❌ Validation failed: ${error instanceof Error ? error.message : String(error)}`);
    }

    console.log("\n" + "=".repeat(60) + "\n");
  }

  // System Statistics
  console.log("📊 System Statistics:");
  console.log("─".repeat(30));
  
  const stats = oracle.getSystemStats();
  
  console.log(`Reference Fingerprint Cache:`);
  console.log(`  Size: ${stats.referenceFingerprint.size}`);
  console.log(`  Hit Rate: ${(stats.referenceFingerprint.hitRate * 100).toFixed(1)}%`);
  
  console.log(`\nInvariant Verifier Cache:`);
  console.log(`  Size: ${stats.invariantVerifier.size}`);
  console.log(`  Hit Rate: ${(stats.invariantVerifier.hitRate * 100).toFixed(1)}%`);
  
  console.log(`\nAdaptive Scoring Cache:`);
  console.log(`  Size: ${stats.adaptiveScoring.size}`);
  console.log(`  Hit Rate: ${(stats.adaptiveScoring.hitRate * 100).toFixed(1)}%`);
  
  console.log(`\nPerformance Calibration:`);
  console.log(`  Total Actions: ${stats.performanceCalibration.totalActions}`);
  console.log(`  Successful Actions: ${stats.performanceCalibration.successfulActions}`);
  console.log(`  Average Impact: ${stats.performanceCalibration.averageImpact.toFixed(3)}`);
  console.log(`  Performance History: ${stats.performanceCalibration.performanceHistoryLength} snapshots`);
  
  console.log(`\nMetrics:`);
  console.log(`  Counters: ${Object.keys(stats.metrics.counters).length}`);
  console.log(`  Gauges: ${Object.keys(stats.metrics.gauges).length}`);
  console.log(`  Histograms: ${Object.keys(stats.metrics.hist).length}`);
  console.log(`  Violations: ${stats.metrics.violations}`);

  // Cleanup
  console.log("\n🧹 Cleaning up...");
  oracle.clearCaches();
  console.log("✅ Cleanup completed");

  console.log("\n🎉 Enhanced Oracle Demonstration Complete!");
  console.log("==========================================");
}

// Run demonstration
if (require.main === module) {
  demonstrateEnhancedOracle().catch(error => {
    console.error("💥 Demonstration failed:", error);
    process.exit(1);
  });
}

export { demonstrateEnhancedOracle };

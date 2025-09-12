#!/usr/bin/env ts-node

import { Metrics } from '../../src/monitoring/metrics/Metrics';
import { StrictHolographicCoherenceOracle } from '../../src/validator/StrictHolographicCoherenceOracle';
import fs from 'node:fs';
import path from 'node:path';

/**
 * Validation script for the Strict Holographic Coherence Oracle
 * 
 * This script validates the implementation against the hologram_generator_mini
 * reference and ensures all holographic coherence invariants are maintained.
 */

async function validateStrictOracle(): Promise<void> {
  console.log('🔍 Validating Strict Holographic Coherence Oracle Implementation');
  console.log('=' .repeat(60));

  const metrics = new Metrics();
  const oracle = new StrictHolographicCoherenceOracle(metrics, {
    enableRealTimeMonitoring: true,
    monitoringIntervalMs: 1000,
    coherenceThreshold: 0.95,
    enableAdaptiveScoring: true,
    enablePerformanceCalibration: true,
    enableReferenceFingerprinting: true,
    maxViolationHistory: 1000,
    enableTrendAnalysis: true
  });

  try {
    // Test 1: Validate example modules
    console.log('\n📦 Test 1: Validating Example Modules');
    console.log('-'.repeat(40));

    const exampleModules = [
      'modules/example-good.json',
      'modules/example-bad.json'
    ];

    for (const modulePath of exampleModules) {
      if (fs.existsSync(modulePath)) {
        console.log(`\n  Validating: ${modulePath}`);
        const result = await oracle.validateModuleStrict(modulePath);
        
        console.log(`    ✅ Valid: ${result.ok ? '✅' : '❌'}`);
        console.log(`    📈 Oracle Score: ${result.oracle_score.toFixed(4)}`);
        console.log(`    🎯 Coherence Score: ${result.coherenceScore.toFixed(4)}`);
        console.log(`    ⚠️  Violations: ${result.violations.length}`);
        console.log(`    ⏱️  Execution Time: ${result.executionTimeMs}ms`);
        
        if (result.violations.length > 0) {
          console.log(`    📋 Violations:`);
          result.violations.forEach((violation: any, index: number) => {
            console.log(`      ${index + 1}. ${violation.type} (${violation.severity}): ${violation.message}`);
          });
        }
      } else {
        console.log(`  ⚠️  Module not found: ${modulePath}`);
      }
    }

    // Test 2: Validate blueprint
    console.log('\n📋 Test 2: Validating Blueprint');
    console.log('-'.repeat(40));

    const blueprintPath = 'atlas-12288/blueprint/blueprint.json';
    if (fs.existsSync(blueprintPath)) {
      console.log(`\n  Validating blueprint: ${blueprintPath}`);
      
      const blueprint = JSON.parse(fs.readFileSync(blueprintPath, 'utf8'));
      
      if (blueprint.modules && Array.isArray(blueprint.modules)) {
        let totalCoherenceScore = 0;
        let validModules = 0;
        let totalViolations = 0;

        for (const module of blueprint.modules) {
          if (typeof module === 'string') {
            const modulePath = path.resolve(path.dirname(blueprintPath), module);
            if (fs.existsSync(modulePath)) {
              console.log(`    📦 Validating module: ${module}`);
              
              const result = await oracle.validateModuleStrict(modulePath);
              totalCoherenceScore += result.coherenceScore;
              totalViolations += result.violations.length;
              
              if (result.ok) {
                validModules++;
              }
              
              console.log(`      Coherence: ${result.coherenceScore.toFixed(4)}, Valid: ${result.ok ? '✅' : '❌'}, Violations: ${result.violations.length}`);
            } else {
              console.log(`    ⚠️  Module not found: ${modulePath}`);
            }
          }
        }

        const averageCoherenceScore = blueprint.modules.length > 0 ? totalCoherenceScore / blueprint.modules.length : 0;
        const blueprintValid = validModules === blueprint.modules.length && averageCoherenceScore >= 0.95;

        console.log(`\n  📊 Blueprint Summary:`);
        console.log(`    ✅ Valid modules: ${validModules}/${blueprint.modules.length}`);
        console.log(`    📈 Average coherence score: ${averageCoherenceScore.toFixed(4)}`);
        console.log(`    ⚠️  Total violations: ${totalViolations}`);
        console.log(`    🎯 Blueprint valid: ${blueprintValid ? '✅' : '❌'}`);
      } else {
        console.log(`  ⚠️  Invalid blueprint: missing modules array`);
      }
    } else {
      console.log(`  ⚠️  Blueprint not found: ${blueprintPath}`);
    }

    // Test 3: Real-time monitoring
    console.log('\n⏱️  Test 3: Real-time Monitoring');
    console.log('-'.repeat(40));

    console.log('  🚀 Starting real-time monitoring for 5 seconds...');
    oracle.startRealTimeMonitoring();

    // Monitor for 5 seconds
    await new Promise(resolve => setTimeout(resolve, 5000));

    oracle.stopRealTimeMonitoring();
    console.log('  🛑 Real-time monitoring stopped');

    // Test 4: Performance characteristics
    console.log('\n⚡ Test 4: Performance Characteristics');
    console.log('-'.repeat(40));

    const testModulePath = 'modules/example-good.json';
    if (fs.existsSync(testModulePath)) {
      const iterations = 10;
      const times: number[] = [];

      console.log(`  🔄 Running ${iterations} validation iterations...`);

      for (let i = 0; i < iterations; i++) {
        const startTime = Date.now();
        await oracle.validateModuleStrict(testModulePath);
        const endTime = Date.now();
        times.push(endTime - startTime);
      }

      const avgTime = times.reduce((sum, time) => sum + time, 0) / times.length;
      const minTime = Math.min(...times);
      const maxTime = Math.max(...times);

      console.log(`  📊 Performance Results:`);
      console.log(`    Average time: ${avgTime.toFixed(2)}ms`);
      console.log(`    Min time: ${minTime}ms`);
      console.log(`    Max time: ${maxTime}ms`);
      console.log(`    Throughput: ${(1000 / avgTime).toFixed(2)} validations/second`);
    }

    // Test 5: Coherence metrics validation
    console.log('\n🎯 Test 5: Coherence Metrics Validation');
    console.log('-'.repeat(40));

    if (fs.existsSync(testModulePath)) {
      const result = await oracle.validateModuleStrict(testModulePath);

      console.log(`  📊 Real-time Metrics:`);
      console.log(`    Coherence Level: ${result.realTimeMetrics.coherenceLevel.toFixed(4)}`);
      console.log(`    Stability Index: ${result.realTimeMetrics.stabilityIndex.toFixed(4)}`);
      console.log(`    Resonance Frequency: ${result.realTimeMetrics.resonanceFrequency}Hz`);
      console.log(`    Holographic Integrity: ${result.realTimeMetrics.holographicIntegrity.toFixed(4)}`);
      console.log(`    Energy Efficiency: ${result.realTimeMetrics.energyEfficiency.toFixed(4)}`);
      console.log(`    Memory Coherence: ${result.realTimeMetrics.memoryCoherence.toFixed(4)}`);
      console.log(`    Phase Alignment: ${result.realTimeMetrics.phaseAlignment.toFixed(4)}`);
      console.log(`    Interference Level: ${result.realTimeMetrics.interferenceLevel.toFixed(4)}`);

      console.log(`\n  🔍 Holographic Correspondence:`);
      console.log(`    Correspondence Score: ${result.holographicCorrespondence.correspondenceScore.toFixed(4)}`);
      console.log(`    Structural Integrity: ${result.holographicCorrespondence.structuralIntegrity.toFixed(4)}`);
      console.log(`    Pattern Consistency: ${result.holographicCorrespondence.patternConsistency.toFixed(4)}`);
      console.log(`    Self-similarity: ${result.holographicCorrespondence.selfSimilarity.toFixed(4)}`);
      console.log(`    Violations: ${result.holographicCorrespondence.correspondenceViolations}`);

      console.log(`\n  🎵 Resonance Classification:`);
      console.log(`    R96 Classification: ${result.resonanceClassification.r96Classification}`);
      console.log(`    Resonance Stability: ${result.resonanceClassification.resonanceStability.toFixed(4)}`);
      console.log(`    Harmonic Alignment: ${result.resonanceClassification.harmonicAlignment.toFixed(4)}`);
      console.log(`    Frequency Coherence: ${result.resonanceClassification.frequencyCoherence.toFixed(4)}`);
      console.log(`    Phase Coherence: ${result.resonanceClassification.phaseCoherence.toFixed(4)}`);
      console.log(`    Violations: ${result.resonanceClassification.resonanceViolations}`);

      console.log(`\n  ⚡ Cycle Conservation:`);
      console.log(`    Cycle Efficiency: ${result.cycleConservation.cycleEfficiency.toFixed(4)}`);
      console.log(`    Energy Conservation: ${result.cycleConservation.energyConservation.toFixed(4)}`);
      console.log(`    Computational Integrity: ${result.cycleConservation.computationalIntegrity.toFixed(4)}`);
      console.log(`    Resource Utilization: ${result.cycleConservation.resourceUtilization.toFixed(4)}`);
      console.log(`    Violations: ${result.cycleConservation.cycleViolations}`);

      console.log(`\n  📄 Page Conservation:`);
      console.log(`    Memory Efficiency: ${result.pageConservation.memoryEfficiency.toFixed(4)}`);
      console.log(`    Page Alignment: ${result.pageConservation.pageAlignment.toFixed(4)}`);
      console.log(`    Memory Coherence: ${result.pageConservation.memoryCoherence.toFixed(4)}`);
      console.log(`    Storage Integrity: ${result.pageConservation.storageIntegrity.toFixed(4)}`);
      console.log(`    Violations: ${result.pageConservation.pageViolations}`);
    }

    // Test 6: System metrics
    console.log('\n📈 Test 6: System Metrics');
    console.log('-'.repeat(40));

    const metricsSnapshot = metrics.snapshot();
    console.log(`  📊 Metrics Summary:`);
    console.log(`    Total violations: ${metricsSnapshot.violations}`);
    console.log(`    Counters: ${Object.keys(metricsSnapshot.counters).length}`);
    console.log(`    Gauges: ${Object.keys(metricsSnapshot.gauges).length}`);
    console.log(`    Histograms: ${Object.keys(metricsSnapshot.hist).length}`);
    console.log(`    Last timestamp: ${metricsSnapshot.lastTs || 'N/A'}`);

    console.log('\n✅ Strict Holographic Coherence Oracle Validation Complete');
    console.log('=' .repeat(60));

  } catch (error) {
    console.error('\n❌ Validation failed:', error);
    process.exit(1);
  }
}

// Run validation if this script is executed directly
if (require.main === module) {
  validateStrictOracle().catch(error => {
    console.error('❌ Validation script failed:', error);
    process.exit(1);
  });
}

export { validateStrictOracle };

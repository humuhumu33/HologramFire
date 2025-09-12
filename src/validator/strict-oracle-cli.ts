#!/usr/bin/env node

import { Command } from 'commander';
import { Metrics } from '../monitoring/metrics/Metrics';
import { StrictHolographicCoherenceOracle, StrictCoherenceResult } from './StrictHolographicCoherenceOracle';
import fs from 'node:fs';
import path from 'node:path';

const program = new Command();

program
  .name('strict-oracle-cli')
  .description('Strict Holographic Coherence Oracle CLI')
  .version('1.0.0');

program
  .command('validate-module')
  .description('Validate a module with strict holographic coherence monitoring')
  .argument('<module-path>', 'Path to the module to validate')
  .option('-v, --verbose', 'Enable verbose output')
  .option('--no-real-time', 'Disable real-time monitoring')
  .option('--no-adaptive-scoring', 'Disable adaptive scoring')
  .option('--no-performance-calibration', 'Disable performance calibration')
  .option('--no-reference-fingerprinting', 'Disable reference fingerprinting')
  .option('--coherence-threshold <threshold>', 'Coherence threshold (0-1)', '0.95')
  .option('--monitoring-interval <ms>', 'Monitoring interval in milliseconds', '1000')
  .option('--output <file>', 'Output results to file')
  .action(async (modulePath: string, options: any) => {
    try {
      const metrics = new Metrics();
      const oracle = new StrictHolographicCoherenceOracle(metrics, {
        enableRealTimeMonitoring: options.realTime,
        enableAdaptiveScoring: options.adaptiveScoring,
        enablePerformanceCalibration: options.performanceCalibration,
        enableReferenceFingerprinting: options.referenceFingerprinting,
        coherenceThreshold: parseFloat(options.coherenceThreshold),
        monitoringIntervalMs: parseInt(options.monitoringInterval)
      });

      console.log(`🔍 Validating module: ${modulePath}`);
      console.log(`📊 Coherence threshold: ${options.coherenceThreshold}`);
      console.log(`⏱️  Monitoring interval: ${options.monitoringInterval}ms`);
      console.log('');

      const result = await oracle.validateModuleStrict(modulePath);

      // Display results
      displayValidationResults(result, options.verbose);

      // Output to file if specified
      if (options.output) {
        const outputData = {
          modulePath,
          timestamp: new Date().toISOString(),
          result
        };
        fs.writeFileSync(options.output, JSON.stringify(outputData, null, 2));
        console.log(`\n📄 Results saved to: ${options.output}`);
      }

      // Exit with appropriate code
      process.exit(result.ok ? 0 : 1);

    } catch (error) {
      console.error('❌ Validation failed:', error);
      process.exit(1);
    }
  });

program
  .command('monitor')
  .description('Start real-time coherence monitoring')
  .option('-v, --verbose', 'Enable verbose output')
  .option('--interval <ms>', 'Monitoring interval in milliseconds', '1000')
  .option('--threshold <threshold>', 'Coherence threshold (0-1)', '0.95')
  .option('--duration <seconds>', 'Monitoring duration in seconds (0 for infinite)', '0')
  .action(async (options: any) => {
    try {
      const metrics = new Metrics();
      const oracle = new StrictHolographicCoherenceOracle(metrics, {
        enableRealTimeMonitoring: true,
        monitoringIntervalMs: parseInt(options.interval),
        coherenceThreshold: parseFloat(options.threshold)
      });

      console.log('🚀 Starting real-time coherence monitoring...');
      console.log(`📊 Coherence threshold: ${options.threshold}`);
      console.log(`⏱️  Monitoring interval: ${options.interval}ms`);
      console.log('');

      oracle.startRealTimeMonitoring();

      // Set up graceful shutdown
      const shutdown = () => {
        console.log('\n🛑 Stopping real-time monitoring...');
        oracle.stopRealTimeMonitoring();
        process.exit(0);
      };

      process.on('SIGINT', shutdown);
      process.on('SIGTERM', shutdown);

      // Monitor for specified duration
      if (options.duration > 0) {
        setTimeout(() => {
          shutdown();
        }, parseInt(options.duration) * 1000);
      }

      // Keep the process alive
      await new Promise(() => {});

    } catch (error) {
      console.error('❌ Monitoring failed:', error);
      process.exit(1);
    }
  });

program
  .command('validate-blueprint')
  .description('Validate an entire blueprint with strict coherence monitoring')
  .argument('<blueprint-path>', 'Path to the blueprint to validate')
  .option('-v, --verbose', 'Enable verbose output')
  .option('--no-real-time', 'Disable real-time monitoring')
  .option('--coherence-threshold <threshold>', 'Coherence threshold (0-1)', '0.95')
  .option('--output <file>', 'Output results to file')
  .action(async (blueprintPath: string, options: any) => {
    try {
      const metrics = new Metrics();
      const oracle = new StrictHolographicCoherenceOracle(metrics, {
        enableRealTimeMonitoring: options.realTime,
        coherenceThreshold: parseFloat(options.coherenceThreshold)
      });

      console.log(`🔍 Validating blueprint: ${blueprintPath}`);
      console.log(`📊 Coherence threshold: ${options.coherenceThreshold}`);
      console.log('');

      // Read blueprint
      const blueprint = JSON.parse(fs.readFileSync(blueprintPath, 'utf8'));
      
      if (!blueprint.modules || !Array.isArray(blueprint.modules)) {
        throw new Error('Invalid blueprint: missing modules array');
      }

      const results: Array<{ module: string; result: StrictCoherenceResult }> = [];
      let totalCoherenceScore = 0;
      let validModules = 0;

      // Validate each module
      for (const module of blueprint.modules) {
        if (typeof module === 'string') {
          const modulePath = path.resolve(path.dirname(blueprintPath), module);
          console.log(`  📦 Validating module: ${module}`);
          
          const result = await oracle.validateModuleStrict(modulePath);
          results.push({ module, result });
          
          if (result.ok) {
            validModules++;
          }
          totalCoherenceScore += result.coherenceScore;
        }
      }

      const averageCoherenceScore = results.length > 0 ? totalCoherenceScore / results.length : 0;
      const blueprintValid = validModules === results.length && averageCoherenceScore >= parseFloat(options.coherenceThreshold);

      // Display results
      console.log('\n📊 Blueprint Validation Results:');
      console.log(`  ✅ Valid modules: ${validModules}/${results.length}`);
      console.log(`  📈 Average coherence score: ${averageCoherenceScore.toFixed(4)}`);
      console.log(`  🎯 Blueprint valid: ${blueprintValid ? '✅' : '❌'}`);
      console.log('');

      if (options.verbose) {
        results.forEach(({ module, result }) => {
          console.log(`  📦 ${module}:`);
          console.log(`    Coherence: ${result.coherenceScore.toFixed(4)}`);
          console.log(`    Valid: ${result.ok ? '✅' : '❌'}`);
          console.log(`    Violations: ${result.violations.length}`);
        });
      }

      // Output to file if specified
      if (options.output) {
        const outputData = {
          blueprintPath,
          timestamp: new Date().toISOString(),
          results,
          summary: {
            totalModules: results.length,
            validModules,
            averageCoherenceScore,
            blueprintValid
          }
        };
        fs.writeFileSync(options.output, JSON.stringify(outputData, null, 2));
        console.log(`\n📄 Results saved to: ${options.output}`);
      }

      // Exit with appropriate code
      process.exit(blueprintValid ? 0 : 1);

    } catch (error) {
      console.error('❌ Blueprint validation failed:', error);
      process.exit(1);
    }
  });

program
  .command('stats')
  .description('Display oracle statistics')
  .option('-v, --verbose', 'Enable verbose output')
  .action(async (options: any) => {
    try {
      const metrics = new Metrics();
      const oracle = new StrictHolographicCoherenceOracle(metrics);

      console.log('📊 Strict Holographic Coherence Oracle Statistics');
      console.log('');

      // Display configuration
      console.log('⚙️  Configuration:');
      console.log(`  Real-time monitoring: ${oracle['config'].enableRealTimeMonitoring ? '✅' : '❌'}`);
      console.log(`  Adaptive scoring: ${oracle['config'].enableAdaptiveScoring ? '✅' : '❌'}`);
      console.log(`  Performance calibration: ${oracle['config'].enablePerformanceCalibration ? '✅' : '❌'}`);
      console.log(`  Reference fingerprinting: ${oracle['config'].enableReferenceFingerprinting ? '✅' : '❌'}`);
      console.log(`  Coherence threshold: ${oracle['config'].coherenceThreshold}`);
      console.log(`  Monitoring interval: ${oracle['config'].monitoringIntervalMs}ms`);
      console.log('');

      // Display metrics
      const metricsSnapshot = metrics.snapshot();
      console.log('📈 System Metrics:');
      console.log(`  Total violations: ${metricsSnapshot.violations}`);
      console.log(`  Counters: ${Object.keys(metricsSnapshot.counters).length}`);
      console.log(`  Gauges: ${Object.keys(metricsSnapshot.gauges).length}`);
      console.log(`  Histograms: ${Object.keys(metricsSnapshot.hist).length}`);
      console.log('');

      if (options.verbose) {
        console.log('🔍 Detailed Metrics:');
        console.log('  Counters:', JSON.stringify(metricsSnapshot.counters, null, 2));
        console.log('  Gauges:', JSON.stringify(metricsSnapshot.gauges, null, 2));
      }

    } catch (error) {
      console.error('❌ Failed to get statistics:', error);
      process.exit(1);
    }
  });

function displayValidationResults(result: StrictCoherenceResult, verbose: boolean): void {
  console.log('📊 Validation Results:');
  console.log(`  ✅ Valid: ${result.ok ? '✅' : '❌'}`);
  console.log(`  📈 Oracle Score: ${result.oracle_score.toFixed(4)}`);
  console.log(`  🎯 Coherence Score: ${result.coherenceScore.toFixed(4)}`);
  console.log(`  ⚠️  Violations: ${result.violations.length}`);
  console.log(`  ⏱️  Execution Time: ${result.executionTimeMs}ms`);
  console.log('');

  if (verbose) {
    console.log('🔍 Real-time Metrics:');
    console.log(`  Coherence Level: ${result.realTimeMetrics.coherenceLevel.toFixed(4)}`);
    console.log(`  Stability Index: ${result.realTimeMetrics.stabilityIndex.toFixed(4)}`);
    console.log(`  Resonance Frequency: ${result.realTimeMetrics.resonanceFrequency}Hz`);
    console.log(`  Holographic Integrity: ${result.realTimeMetrics.holographicIntegrity.toFixed(4)}`);
    console.log(`  Energy Efficiency: ${result.realTimeMetrics.energyEfficiency.toFixed(4)}`);
    console.log(`  Memory Coherence: ${result.realTimeMetrics.memoryCoherence.toFixed(4)}`);
    console.log(`  Phase Alignment: ${result.realTimeMetrics.phaseAlignment.toFixed(4)}`);
    console.log(`  Interference Level: ${result.realTimeMetrics.interferenceLevel.toFixed(4)}`);
    console.log('');

    console.log('🔍 Holographic Correspondence:');
    console.log(`  Correspondence Score: ${result.holographicCorrespondence.correspondenceScore.toFixed(4)}`);
    console.log(`  Structural Integrity: ${result.holographicCorrespondence.structuralIntegrity.toFixed(4)}`);
    console.log(`  Pattern Consistency: ${result.holographicCorrespondence.patternConsistency.toFixed(4)}`);
    console.log(`  Self-similarity: ${result.holographicCorrespondence.selfSimilarity.toFixed(4)}`);
    console.log(`  Violations: ${result.holographicCorrespondence.correspondenceViolations}`);
    console.log('');

    console.log('🔍 Resonance Classification:');
    console.log(`  R96 Classification: ${result.resonanceClassification.r96Classification}`);
    console.log(`  Resonance Stability: ${result.resonanceClassification.resonanceStability.toFixed(4)}`);
    console.log(`  Harmonic Alignment: ${result.resonanceClassification.harmonicAlignment.toFixed(4)}`);
    console.log(`  Frequency Coherence: ${result.resonanceClassification.frequencyCoherence.toFixed(4)}`);
    console.log(`  Phase Coherence: ${result.resonanceClassification.phaseCoherence.toFixed(4)}`);
    console.log(`  Violations: ${result.resonanceClassification.resonanceViolations}`);
    console.log('');

    console.log('🔍 Cycle Conservation:');
    console.log(`  Cycle Efficiency: ${result.cycleConservation.cycleEfficiency.toFixed(4)}`);
    console.log(`  Energy Conservation: ${result.cycleConservation.energyConservation.toFixed(4)}`);
    console.log(`  Computational Integrity: ${result.cycleConservation.computationalIntegrity.toFixed(4)}`);
    console.log(`  Resource Utilization: ${result.cycleConservation.resourceUtilization.toFixed(4)}`);
    console.log(`  Violations: ${result.cycleConservation.cycleViolations}`);
    console.log('');

    console.log('🔍 Page Conservation:');
    console.log(`  Memory Efficiency: ${result.pageConservation.memoryEfficiency.toFixed(4)}`);
    console.log(`  Page Alignment: ${result.pageConservation.pageAlignment.toFixed(4)}`);
    console.log(`  Memory Coherence: ${result.pageConservation.memoryCoherence.toFixed(4)}`);
    console.log(`  Storage Integrity: ${result.pageConservation.storageIntegrity.toFixed(4)}`);
    console.log(`  Violations: ${result.pageConservation.pageViolations}`);
    console.log('');

    if (result.violationTrends.length > 0) {
      console.log('📈 Violation Trends:');
      result.violationTrends.forEach(trend => {
        console.log(`  ${trend.violationType}: ${trend.count} (${trend.trend})`);
      });
      console.log('');
    }

    if (result.violations.length > 0) {
      console.log('⚠️  Violations:');
      result.violations.forEach((violation, index) => {
        console.log(`  ${index + 1}. ${violation.type} (${violation.severity}): ${violation.message}`);
        if (violation.location) {
          console.log(`     Location: ${violation.location}`);
        }
      });
    }
  }
}

program.parse();

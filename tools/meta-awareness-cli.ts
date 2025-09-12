#!/usr/bin/env node

import { Metrics } from '../src/monitoring/metrics/Metrics';
import { Oculus } from '../src/monitoring/meta-self-awareness/Oculus';
import { OculusOverlay } from '../src/monitoring/meta-self-awareness/OculusOverlay';
import { OculusIntegration } from '../src/monitoring/meta-self-awareness/OculusIntegration';
import { ProofChainManager } from '../src/proof-chain/ProofChain';

/**
 * Oculus CLI Tool
 * 
 * Demonstrates the Oculus meta self-awareness layer in action with real-time
 * monitoring and optimization of latency, compute, and energy use.
 */

interface CLIOptions {
  mode: 'monitor' | 'optimize' | 'demo' | 'stats';
  duration?: number;
  interval?: number;
  verbose?: boolean;
  output?: 'console' | 'json' | 'csv';
}

class OculusCLI {
  private metrics: Metrics;
  private proofChainManager: ProofChainManager;
  private oculus: Oculus;
  private overlayWitness: OculusOverlay;
  private integration: OculusIntegration;
  private options: CLIOptions;

  constructor(options: CLIOptions) {
    this.options = options;
    this.metrics = new Metrics();
    this.proofChainManager = new ProofChainManager(this.metrics);

    // Initialize Oculus
    this.oculus = new Oculus({
      enableLatencyOptimization: true,
      enableComputeOptimization: true,
      enableEnergyOptimization: true,
      enableOracleIntegration: true,
      enableMLOptimization: true,
      monitoringIntervalMs: options.interval || 5000,
      optimizationThreshold: 0.1,
      maxOverheadPercent: 0.05,
      enableAdaptiveSampling: true,
      enablePredictiveOptimization: true,
      witnessCompressionRatio: 0.3
    }, this.metrics, this.proofChainManager);

    // Initialize overlay witness
    this.overlayWitness = new OculusOverlay({
      enableMetaAwareness: true,
      enableWitnessVerification: true,
      enableOverlayOptimization: true,
      witnessCompressionRatio: 0.2,
      maxOverheadPercent: 0.03,
      enableAdaptiveOverlay: true,
      overlaySamplingRate: 0.5,
      enablePredictiveWitness: true
    }, this.metrics, this.proofChainManager);

    // Initialize integration
    this.integration = new OculusIntegration({
      enableMetaAwareness: true,
      enableOverlayWitness: true,
      enableSystemIntegration: true,
      enableOracleIntegration: true,
      enableOptimizationIntegration: true,
      enableEnergyIntegration: true,
      integrationMode: 'adaptive',
      maxSystemOverhead: 0.05,
      enablePredictiveIntegration: true,
      enableHolographicIntegration: true
    }, this.metrics, this.proofChainManager);
  }

  async run(): Promise<void> {
    console.log('🔮 Oculus CLI');
    console.log('=====================================');
    console.log(`Mode: ${this.options.mode}`);
    console.log(`Duration: ${this.options.duration || 'unlimited'} seconds`);
    console.log(`Interval: ${this.options.interval || 5000}ms`);
    console.log('');

    try {
      switch (this.options.mode) {
        case 'monitor':
          await this.runMonitoring();
          break;
        case 'optimize':
          await this.runOptimization();
          break;
        case 'demo':
          await this.runDemo();
          break;
        case 'stats':
          await this.showStats();
          break;
        default:
          console.error('Unknown mode:', this.options.mode);
          process.exit(1);
      }
    } catch (error) {
      console.error('Error:', error);
      process.exit(1);
    } finally {
      this.cleanup();
    }
  }

  private async runMonitoring(): Promise<void> {
    console.log('📊 Starting real-time monitoring...');
    console.log('');

    this.integration.activateIntegration();

    const startTime = Date.now();
    const duration = this.options.duration ? this.options.duration * 1000 : Infinity;

    while (Date.now() - startTime < duration) {
      try {
        const result = await this.integration.performSystemOptimization();
        
        if (this.options.verbose) {
          this.displayDetailedResults(result);
        } else {
          this.displaySummaryResults(result);
        }

        await this.sleep(this.options.interval || 5000);
      } catch (error) {
        console.error('Monitoring error:', error);
      }
    }

    console.log('\n📊 Monitoring completed.');
  }

  private async runOptimization(): Promise<void> {
    console.log('⚡ Running system optimization...');
    console.log('');

    this.integration.activateIntegration();

    const startTime = Date.now();
    const result = await this.integration.performSystemOptimization();
    const endTime = Date.now();

    console.log(`⏱️  Optimization completed in ${endTime - startTime}ms`);
    console.log('');

    this.displayOptimizationResults(result);

    this.integration.deactivateIntegration();
  }

  private async runDemo(): Promise<void> {
    console.log('🎯 Running meta awareness demo...');
    console.log('');

    this.integration.activateIntegration();

    // Simulate different system loads
    const scenarios = [
      { name: 'Low Load', operations: 100, delay: 1000 },
      { name: 'Medium Load', operations: 500, delay: 2000 },
      { name: 'High Load', operations: 1000, delay: 3000 },
      { name: 'Peak Load', operations: 2000, delay: 4000 }
    ];

    for (const scenario of scenarios) {
      console.log(`📈 Simulating ${scenario.name}...`);
      
      // Simulate system load
      for (let i = 0; i < scenario.operations; i++) {
        this.metrics.inc('demo_operations', 1);
        this.metrics.observe('demo_latency_ms', Math.random() * 100);
      }

      // Run optimization
      const result = await this.integration.performSystemOptimization();
      
      console.log(`   Latency: ${result.systemOptimizations.latency.toFixed(3)}`);
      console.log(`   Compute: ${result.systemOptimizations.compute.toFixed(3)}`);
      console.log(`   Energy: ${result.systemOptimizations.energy.toFixed(3)}`);
      console.log(`   Overhead: ${(result.integrationOverhead.latency * 100).toFixed(1)}%`);
      console.log('');

      await this.sleep(scenario.delay);
    }

    console.log('🎯 Demo completed.');
    this.integration.deactivateIntegration();
  }

  private async showStats(): Promise<void> {
    console.log('📊 Meta Awareness Statistics');
    console.log('============================');
    console.log('');

    this.integration.activateIntegration();

    // Get integration stats
    const integrationStats = this.integration.getIntegrationStats();
    console.log('Integration Status:');
    console.log(`  Active: ${integrationStats.integrationActive}`);
    console.log(`  Meta Awareness: ${integrationStats.metaAwarenessActive}`);
    console.log(`  Overlay Witness: ${integrationStats.overlayWitnessActive}`);
    console.log(`  Components: ${integrationStats.systemComponentsCount}`);
    console.log('');

    // Get optimization history
    const optimizationHistory = this.integration.getOptimizationHistory();
    console.log('Optimization History:');
    console.log(`  Total Optimizations: ${optimizationHistory.length}`);
    
    if (optimizationHistory.length > 0) {
      const avgImprovement = optimizationHistory.reduce((sum, rec) => sum + rec.expectedImprovement, 0) / optimizationHistory.length;
      console.log(`  Average Improvement: ${(avgImprovement * 100).toFixed(1)}%`);
    }
    console.log('');

    // Get system component status
    const componentStatus = this.integration.getSystemComponentStatus();
    console.log('System Components:');
    for (const [name, status] of Object.entries(componentStatus)) {
      console.log(`  ${name}: ${status.status || 'active'}`);
    }
    console.log('');

    // Get overlay stats
    const overlayStats = this.overlayWitness.getOverlayStats();
    console.log('Overlay Witness:');
    console.log(`  Active: ${overlayStats.overlayActive}`);
    console.log(`  Cache Size: ${overlayStats.witnessCacheSize}`);
    console.log(`  Adaptive Rate: ${overlayStats.adaptiveOverlayRate.toFixed(3)}`);
    console.log('');

    this.integration.deactivateIntegration();
  }

  private displaySummaryResults(result: any): void {
    const timestamp = new Date().toLocaleTimeString();
    const latency = result.systemOptimizations.latency.toFixed(3);
    const compute = result.systemOptimizations.compute.toFixed(3);
    const energy = result.systemOptimizations.energy.toFixed(3);
    const overhead = (result.integrationOverhead.latency * 100).toFixed(1);

    console.log(`[${timestamp}] Latency: ${latency} | Compute: ${compute} | Energy: ${energy} | Overhead: ${overhead}%`);
  }

  private displayDetailedResults(result: any): void {
    const timestamp = new Date().toLocaleTimeString();
    console.log(`\n[${timestamp}] Meta Awareness Results:`);
    console.log('=====================================');
    
    // System metrics
    console.log('System Metrics:');
    console.log(`  Latency: ${result.systemMetrics.latency.current.toFixed(2)}ms (trend: ${result.systemMetrics.latency.trend})`);
    console.log(`  Compute Efficiency: ${result.systemMetrics.compute.efficiency.toFixed(3)}`);
    console.log(`  Energy Efficiency: ${result.systemMetrics.energy.efficiency.toFixed(3)}`);
    console.log('');

    // Optimization decisions
    console.log('Optimization Decisions:');
    if (result.optimizationDecisions.length === 0) {
      console.log('  No optimizations needed');
    } else {
      for (const decision of result.optimizationDecisions) {
        console.log(`  ${decision.type}: ${decision.action} (${(decision.expectedImprovement * 100).toFixed(1)}% improvement)`);
      }
    }
    console.log('');

    // Performance gains
    console.log('Performance Gains:');
    console.log(`  Latency: ${(result.performanceGains.latency * 100).toFixed(1)}%`);
    console.log(`  Compute: ${(result.performanceGains.compute * 100).toFixed(1)}%`);
    console.log(`  Energy: ${(result.performanceGains.energy * 100).toFixed(1)}%`);
    console.log('');

    // Overhead
    console.log('Overhead:');
    console.log(`  Latency: ${(result.overhead.latency * 100).toFixed(2)}%`);
    console.log(`  Compute: ${(result.overhead.compute * 100).toFixed(2)}%`);
    console.log(`  Energy: ${(result.overhead.energy * 100).toFixed(2)}%`);
    console.log('');
  }

  private displayOptimizationResults(result: any): void {
    console.log('Optimization Results:');
    console.log('====================');
    console.log(`Latency Improvement: ${(result.systemOptimizations.latency * 100).toFixed(1)}%`);
    console.log(`Compute Improvement: ${(result.systemOptimizations.compute * 100).toFixed(1)}%`);
    console.log(`Energy Improvement: ${(result.systemOptimizations.energy * 100).toFixed(1)}%`);
    console.log('');
    console.log('Integration Overhead:');
    console.log(`Latency: ${(result.integrationOverhead.latency * 100).toFixed(2)}%`);
    console.log(`Compute: ${(result.integrationOverhead.compute * 100).toFixed(2)}%`);
    console.log(`Energy: ${(result.integrationOverhead.energy * 100).toFixed(2)}%`);
    console.log('');
  }

  private cleanup(): void {
    this.oculus.stopMonitoring();
    this.overlayWitness.deactivateOverlay();
    this.integration.deactivateIntegration();
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

// CLI argument parsing
function parseArgs(): CLIOptions {
  const args = process.argv.slice(2);
  const options: CLIOptions = {
    mode: 'demo'
  };

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    
    switch (arg) {
      case '--mode':
      case '-m':
        options.mode = args[++i] as any;
        break;
      case '--duration':
      case '-d':
        options.duration = parseInt(args[++i]);
        break;
      case '--interval':
      case '-i':
        options.interval = parseInt(args[++i]);
        break;
      case '--verbose':
      case '-v':
        options.verbose = true;
        break;
      case '--output':
      case '-o':
        options.output = args[++i] as any;
        break;
      case '--help':
      case '-h':
        showHelp();
        process.exit(0);
        break;
    }
  }

  return options;
}

function showHelp(): void {
  console.log('Oculus CLI');
  console.log('');
  console.log('Usage: node meta-awareness-cli.js [options]');
  console.log('');
  console.log('Options:');
  console.log('  -m, --mode <mode>      Mode: monitor, optimize, demo, stats (default: demo)');
  console.log('  -d, --duration <sec>   Duration in seconds (default: unlimited)');
  console.log('  -i, --interval <ms>    Monitoring interval in milliseconds (default: 5000)');
  console.log('  -v, --verbose          Verbose output');
  console.log('  -o, --output <format>  Output format: console, json, csv (default: console)');
  console.log('  -h, --help             Show this help message');
  console.log('');
  console.log('Examples:');
  console.log('  node meta-awareness-cli.js --mode monitor --duration 60');
  console.log('  node meta-awareness-cli.js --mode optimize --verbose');
  console.log('  node meta-awareness-cli.js --mode demo --interval 2000');
  console.log('  node meta-awareness-cli.js --mode stats');
}

// Main execution
if (require.main === module) {
  const options = parseArgs();
  const cli = new OculusCLI(options);
  cli.run().catch(console.error);
}

export { OculusCLI };

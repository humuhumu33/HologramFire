#!/usr/bin/env node

/**
 * Oculus Example
 * 
 * Demonstrates the Oculus meta self-awareness layer monitoring and optimizing
 * a simulated hologram system with real-time feedback.
 */

import { Metrics } from '../src/monitoring/metrics/Metrics';
import { OculusIntegration } from '../src/monitoring/meta-self-awareness/OculusIntegration';
import { ProofChainManager } from '../src/proof-chain/ProofChain';

class HologramSystemSimulator {
  private metrics: Metrics;
  private isRunning: boolean = false;
  private operationCount: number = 0;

  constructor(metrics: Metrics) {
    this.metrics = metrics;
  }

  start(): void {
    this.isRunning = true;
    this.simulateOperations();
  }

  stop(): void {
    this.isRunning = false;
  }

  private simulateOperations(): void {
    if (!this.isRunning) return;

    // Simulate various types of operations
    const operations = [
      () => this.simulateHologramGeneration(),
      () => this.simulateProofVerification(),
      () => this.simulateDataTransformation(),
      () => this.simulateCryptographicOperation()
    ];

    const operation = operations[Math.floor(Math.random() * operations.length)];
    operation();

    // Schedule next operation
    const delay = Math.random() * 100 + 50; // 50-150ms delay
    setTimeout(() => this.simulateOperations(), delay);
  }

  private simulateHologramGeneration(): void {
    const startTime = Date.now();
    
    // Simulate hologram generation work
    const workTime = Math.random() * 50 + 20; // 20-70ms
    setTimeout(() => {
      const latency = Date.now() - startTime;
      this.metrics.observe('hologram_generation_latency_ms', latency);
      this.metrics.inc('hologram_generations', 1);
      this.metrics.inc('total_operations', 1);
      this.operationCount++;
    }, workTime);
  }

  private simulateProofVerification(): void {
    const startTime = Date.now();
    
    // Simulate proof verification work
    const workTime = Math.random() * 30 + 10; // 10-40ms
    setTimeout(() => {
      const latency = Date.now() - startTime;
      this.metrics.observe('proof_verification_latency_ms', latency);
      this.metrics.inc('proof_verifications', 1);
      this.metrics.inc('total_operations', 1);
      this.operationCount++;
    }, workTime);
  }

  private simulateDataTransformation(): void {
    const startTime = Date.now();
    
    // Simulate data transformation work
    const workTime = Math.random() * 40 + 15; // 15-55ms
    setTimeout(() => {
      const latency = Date.now() - startTime;
      this.metrics.observe('data_transformation_latency_ms', latency);
      this.metrics.inc('data_transformations', 1);
      this.metrics.inc('total_operations', 1);
      this.operationCount++;
    }, workTime);
  }

  private simulateCryptographicOperation(): void {
    const startTime = Date.now();
    
    // Simulate cryptographic operation work
    const workTime = Math.random() * 60 + 25; // 25-85ms
    setTimeout(() => {
      const latency = Date.now() - startTime;
      this.metrics.observe('crypto_operation_latency_ms', latency);
      this.metrics.inc('crypto_operations', 1);
      this.metrics.inc('total_operations', 1);
      this.operationCount++;
    }, workTime);
  }

  getOperationCount(): number {
    return this.operationCount;
  }
}

class OculusExample {
  private metrics: Metrics;
  private proofChainManager: ProofChainManager;
  private integration: OculusIntegration;
  private simulator: HologramSystemSimulator;
  private isRunning: boolean = false;

  constructor() {
    this.metrics = new Metrics();
    this.proofChainManager = new ProofChainManager(this.metrics);
    
    // Initialize Oculus integration
    this.integration = new OculusIntegration({
      enableMetaAwareness: true,
      enableOverlayWitness: true,
      enableSystemIntegration: true,
      enableOracleIntegration: true,
      enableOptimizationIntegration: true,
      enableEnergyIntegration: true,
      integrationMode: 'adaptive',
      maxSystemOverhead: 0.05, // 5% max overhead
      enablePredictiveIntegration: true,
      enableHolographicIntegration: true
    }, this.metrics, this.proofChainManager);

    this.simulator = new HologramSystemSimulator(this.metrics);
  }

  async run(durationSeconds: number = 60): Promise<void> {
    console.log('🔮 Oculus Example');
    console.log('=====================================');
    console.log(`Running for ${durationSeconds} seconds...`);
    console.log('');

    this.isRunning = true;
    this.integration.activateIntegration();
    this.simulator.start();

    const startTime = Date.now();
    const endTime = startTime + (durationSeconds * 1000);

    // Run optimization cycles
    while (Date.now() < endTime && this.isRunning) {
      try {
        await this.runOptimizationCycle();
        await this.sleep(5000); // 5 second intervals
      } catch (error) {
        console.error('Optimization cycle error:', error);
      }
    }

    this.cleanup();
    this.showFinalResults();
  }

  private async runOptimizationCycle(): Promise<void> {
    const cycleStart = Date.now();
    
    // Perform system optimization
    const result = await this.integration.performSystemOptimization();
    
    const cycleTime = Date.now() - cycleStart;
    const timestamp = new Date().toLocaleTimeString();
    
    // Display results
    console.log(`[${timestamp}] Optimization Cycle (${cycleTime}ms)`);
    console.log('----------------------------------------');
    
    // System metrics
    console.log('System Metrics:');
    console.log(`  Latency: ${result.systemMetrics.latency.current.toFixed(2)}ms (${result.systemMetrics.latency.trend})`);
    console.log(`  Compute Efficiency: ${result.systemMetrics.compute.efficiency.toFixed(3)}`);
    console.log(`  Energy Efficiency: ${result.systemMetrics.energy.efficiency.toFixed(3)}`);
    console.log('');
    
    // Optimization decisions
    if (result.optimizationDecisions.length > 0) {
      console.log('Optimization Decisions:');
      for (const decision of result.optimizationDecisions) {
        console.log(`  ${decision.type}: ${decision.action} (${(decision.expectedImprovement * 100).toFixed(1)}% improvement)`);
      }
      console.log('');
    }
    
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
    
    // Operations count
    console.log(`Total Operations: ${this.simulator.getOperationCount()}`);
    console.log('');
  }

  private showFinalResults(): void {
    console.log('📊 Final Results');
    console.log('================');
    console.log('');
    
    // Integration stats
    const integrationStats = this.integration.getIntegrationStats();
    console.log('Integration Statistics:');
    console.log(`  Total Optimizations: ${integrationStats.optimizationHistoryLength}`);
    console.log(`  System Components: ${integrationStats.systemComponentsCount}`);
    console.log(`  Last Integration: ${new Date(integrationStats.lastIntegrationTime).toLocaleTimeString()}`);
    console.log('');
    
    // Optimization history
    const optimizationHistory = this.integration.getOptimizationHistory();
    if (optimizationHistory.length > 0) {
      console.log('Optimization History:');
      const avgImprovement = optimizationHistory.reduce((sum, rec) => sum + rec.expectedImprovement, 0) / optimizationHistory.length;
      console.log(`  Average Improvement: ${(avgImprovement * 100).toFixed(1)}%`);
      
      const optimizationTypes: { [key: string]: number } = {};
      for (const rec of optimizationHistory) {
        optimizationTypes[rec.component] = (optimizationTypes[rec.component] || 0) + 1;
      }
      
      console.log('  Optimization Types:');
      for (const [type, count] of Object.entries(optimizationTypes)) {
        console.log(`    ${type}: ${count}`);
      }
      console.log('');
    }
    
    // System component status
    const componentStatus = this.integration.getSystemComponentStatus();
    console.log('System Component Status:');
    for (const [name, status] of Object.entries(componentStatus)) {
      console.log(`  ${name}: ${status.status || 'active'}`);
    }
    console.log('');
    
    // Final metrics
    const snapshot = this.metrics.snapshot();
    console.log('Final Metrics:');
    console.log(`  Total Operations: ${snapshot.counters['total_operations'] || 0}`);
    console.log(`  Hologram Generations: ${snapshot.counters['hologram_generations'] || 0}`);
    console.log(`  Proof Verifications: ${snapshot.counters['proof_verifications'] || 0}`);
    console.log(`  Data Transformations: ${snapshot.counters['data_transformations'] || 0}`);
    console.log(`  Crypto Operations: ${snapshot.counters['crypto_operations'] || 0}`);
    console.log('');
    
    console.log('🎯 Example completed successfully!');
  }

  private cleanup(): void {
    this.isRunning = false;
    this.simulator.stop();
    this.integration.deactivateIntegration();
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

// Main execution
async function main(): Promise<void> {
  const duration = process.argv[2] ? parseInt(process.argv[2]) : 60;
  
  if (isNaN(duration) || duration <= 0) {
    console.error('Invalid duration. Please provide a positive number of seconds.');
    process.exit(1);
  }

  const example = new OculusExample();
  
  try {
    await example.run(duration);
  } catch (error) {
    console.error('Example failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main().catch(console.error);
}

export { OculusExample };

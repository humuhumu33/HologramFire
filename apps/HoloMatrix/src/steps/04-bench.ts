/**
 * Benchmark Step - Throughput and Latency Validation
 * Runs comprehensive benchmarks and validates acceptance gates
 */

import { program } from 'commander';
import type { BenchConfig, Metrics } from '../types';
import { runLoadGen, type LoadGenResult } from '../bench/loadgen';
import { createReporter, type PerformanceReporter } from '../bench/report';
import { TransportStep } from './01-transport';
import { StorageStep } from './02-storage';
import { ComputeStep } from './03-compute';
import { budget } from '../testkit';

export interface BenchStepResult {
  success: boolean;
  allGatesPassed: boolean;
  metrics: Metrics;
  loadGenResult: LoadGenResult;
  gateResults: Array<{
    name: string;
    passed: boolean;
    actual: number;
    operator: string;
    threshold: number;
  }>;
}

export class BenchStep {
  private config: BenchConfig;
  private reporter: PerformanceReporter;

  constructor(config: BenchConfig) {
    this.config = config;
    this.reporter = createReporter({ format: 'both' });
  }

  /**
   * Run comprehensive benchmark suite
   */
  async runBenchmark(): Promise<BenchStepResult> {
    console.log('🚀 Starting Hologram Matrix Multiplication Benchmark');
    console.log('='.repeat(60));
    console.log(`Configuration:`);
    console.log(`  Duration: ${this.config.duration}s`);
    console.log(`  Lanes: ${this.config.lanes}`);
    console.log(`  Payload: ${this.config.payload}B`);
    console.log(`  Batch: ${this.config.batch}`);
    console.log(`  Workers: ${this.config.workers}`);
    console.log(`  Window: ${this.config.window}ms`);
    console.log(`  Target: ${this.config.target} Gbit/s`);
    console.log('='.repeat(60));

    const startTime = Date.now();

    try {
      // Run load generation test
      console.log('\n📊 Running Load Generation Test...');
      const loadGenResult = await runLoadGen(this.config);

      // Run individual component tests
      console.log('\n🚛 Running Transport Component Test...');
      const transportResult = await this.runTransportTest();

      console.log('\n💾 Running Storage Component Test...');
      const storageResult = await this.runStorageTest();

      console.log('\n⚡ Running Compute Component Test...');
      const computeResult = await this.runComputeTest();

      // Aggregate metrics
      const metrics = this.aggregateMetrics(loadGenResult, transportResult, storageResult, computeResult);

      // Check acceptance gates
      const gateResults = this.checkAcceptanceGates(metrics);
      const allGatesPassed = gateResults.every(gate => gate.passed);

      const result: BenchStepResult = {
        success: true,
        allGatesPassed,
        metrics,
        loadGenResult,
        gateResults
      };

      // Generate report
      this.reporter.generateReport(metrics, loadGenResult);

      const duration = (Date.now() - startTime) / 1000;
      console.log(`\n⏱️  Benchmark completed in ${duration.toFixed(2)}s`);

      return result;
    } catch (error) {
      console.error('Benchmark failed:', error);
      throw error;
    }
  }

  private async runTransportTest(): Promise<{
    p50Ms: number;
    p99Ms: number;
    framesSent: number;
    framesReceived: number;
    windowsTotal: number;
    windowsClosed: number;
    rejects: number;
  }> {
    const transport = new TransportStep({
      lanes: this.config.lanes,
      windowMs: this.config.window,
      budget: budget(1000, 1000, 1000)
    });

    try {
      await transport.initialize();
      await transport.handshake();

      const result = await transport.runStressTest({
        duration: Math.min(5, this.config.duration), // Shorter test for component
        framesPerSecond: 50,
        payloadSize: this.config.payload
      });

      return {
        p50Ms: result.metrics.sendLatency.p50(),
        p99Ms: result.metrics.sendLatency.p99(),
        framesSent: result.metrics.framesSent,
        framesReceived: result.metrics.framesReceived,
        windowsTotal: result.metrics.windowsTotal,
        windowsClosed: result.metrics.windowsClosed,
        rejects: result.metrics.rejects
      };
    } finally {
      await transport.close();
    }
  }

  private async runStorageTest(): Promise<{
    p50Ms: number;
    p99Ms: number;
    puts: number;
    gets: number;
    repairs: number;
  }> {
    const storage = new StorageStep({
      budget: budget(1000, 1000, 1000)
    });

    try {
      await storage.initialize();

      const result = await storage.runStressTest({
        duration: Math.min(5, this.config.duration), // Shorter test for component
        operationsPerSecond: 20,
        dataSize: this.config.payload
      });

      return {
        p50Ms: result.metrics.putLatency.p50(),
        p99Ms: result.metrics.putLatency.p99(),
        puts: result.metrics.puts,
        gets: result.metrics.gets,
        repairs: result.metrics.repairs
      };
    } finally {
      await storage.close();
    }
  }

  private async runComputeTest(): Promise<{
    p50Ms: number;
    p99Ms: number;
    kernels: number;
    receipts: number;
  }> {
    const compute = new ComputeStep({
      budget: budget(1000, 1000, 1000)
    });

    try {
      await compute.initialize();

      const result = await compute.runStressTest({
        duration: Math.min(5, this.config.duration), // Shorter test for component
        kernelsPerSecond: 5,
        inputCount: 3
      });

      return {
        p50Ms: result.metrics.computeLatency.p50(),
        p99Ms: result.metrics.computeLatency.p99(),
        kernels: result.metrics.kernels,
        receipts: result.metrics.receipts
      };
    } finally {
      await compute.close();
    }
  }

  private aggregateMetrics(
    loadGenResult: LoadGenResult,
    transportResult: any,
    storageResult: any,
    computeResult: any
  ): Metrics {
    return {
      throughputGbps: loadGenResult.throughputGbps,
      transport: {
        p50Ms: transportResult.p50Ms,
        p99Ms: transportResult.p99Ms,
        framesSent: transportResult.framesSent,
        framesReceived: transportResult.framesReceived,
        windowsTotal: transportResult.windowsTotal,
        windowsClosed: transportResult.windowsClosed,
        rejects: transportResult.rejects
      },
      storage: {
        p50Ms: storageResult.p50Ms,
        p99Ms: storageResult.p99Ms,
        puts: storageResult.puts,
        gets: storageResult.gets,
        repairs: storageResult.repairs
      },
      compute: {
        p50Ms: computeResult.p50Ms,
        p99Ms: computeResult.p99Ms,
        kernels: computeResult.kernels,
        receipts: computeResult.receipts
      },
      e2e: {
        p50Ms: Math.max(transportResult.p50Ms, storageResult.p50Ms, computeResult.p50Ms),
        p99Ms: Math.max(transportResult.p99Ms, storageResult.p99Ms, computeResult.p99Ms)
      }
    };
  }

  private checkAcceptanceGates(metrics: Metrics): Array<{
    name: string;
    passed: boolean;
    actual: number;
    operator: string;
    threshold: number;
  }> {
    return [
      {
        name: 'Throughput ≥ 25.0 Gbit/s',
        passed: metrics.throughputGbps >= 25.0,
        actual: metrics.throughputGbps,
        operator: '>=',
        threshold: 25.0
      },
      {
        name: 'Transport p99 ≤ 1.8 ms',
        passed: metrics.transport.p99Ms <= 1.8,
        actual: metrics.transport.p99Ms,
        operator: '<=',
        threshold: 1.8
      },
      {
        name: 'Storage p99 ≤ 3.0 ms',
        passed: metrics.storage.p99Ms <= 3.0,
        actual: metrics.storage.p99Ms,
        operator: '<=',
        threshold: 3.0
      },
      {
        name: 'Compute p99 ≤ 10.0 ms',
        passed: metrics.compute.p99Ms <= 10.0,
        actual: metrics.compute.p99Ms,
        operator: '<=',
        threshold: 10.0
      },
      {
        name: 'E2E p99 ≤ 20.0 ms',
        passed: metrics.e2e.p99Ms <= 20.0,
        actual: metrics.e2e.p99Ms,
        operator: '<=',
        threshold: 20.0
      },
      {
        name: 'Window closure ≥ 99.5%',
        passed: (metrics.transport.windowsClosed / metrics.transport.windowsTotal) >= 0.995,
        actual: (metrics.transport.windowsClosed / metrics.transport.windowsTotal) * 100,
        operator: '>=',
        threshold: 99.5
      },
      {
        name: 'Reject rate ≤ 2%',
        passed: (metrics.transport.rejects / metrics.transport.framesSent) <= 0.02,
        actual: (metrics.transport.rejects / metrics.transport.framesSent) * 100,
        operator: '<=',
        threshold: 2.0
      }
    ];
  }
}

// CLI interface
if (require.main === module) {
  program
    .option('-d, --duration <seconds>', 'Test duration in seconds', '10')
    .option('-l, --lanes <count>', 'Number of lanes', '64')
    .option('-p, --payload <bytes>', 'Payload size in bytes', '4096')
    .option('-b, --batch <count>', 'Batch size', '16')
    .option('-w, --workers <count>', 'Number of workers', '4')
    .option('-W, --window <ms>', 'Window size in milliseconds', '100')
    .option('-t, --target <gbps>', 'Target throughput in Gbit/s', '25')
    .parse();

  const options = program.opts();

  const config: BenchConfig = {
    duration: parseInt(options['duration']),
    lanes: parseInt(options['lanes']),
    payload: parseInt(options['payload']),
    batch: parseInt(options['batch']),
    workers: parseInt(options['workers']),
    window: parseInt(options['window']),
    target: parseInt(options['target'])
  };

  async function main() {
    const bench = new BenchStep(config);
    
    try {
      const result = await bench.runBenchmark();
      
      console.log('\n🎯 Final Results:');
      console.log(`All gates passed: ${result.allGatesPassed ? '✅ YES' : '❌ NO'}`);
      
      if (!result.allGatesPassed) {
        console.log('\nFailed gates:');
        result.gateResults
          .filter(gate => !gate.passed)
          .forEach(gate => {
            console.log(`  ❌ ${gate.name}: ${gate.actual} ${gate.operator} ${gate.threshold}`);
          });
        
        process.exit(1);
      } else {
        console.log('🎉 All acceptance gates passed!');
        process.exit(0);
      }
    } catch (error) {
      console.error('Benchmark failed:', error);
      process.exit(1);
    }
  }

  main();
}

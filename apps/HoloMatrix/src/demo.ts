/**
 * Hologram Matrix Multiplication Demo Orchestrator
 * Main entry point for the end-to-end hologram virtual infra matmul demo
 */

import { program } from 'commander';
import { BenchStep } from './steps/04-bench';
import { MatMulStep } from './steps/05-matmul';
import { createDefaultMatMulConfig } from './usecases/matmul';
import type { BenchConfig, MatMulConfig } from './types';

export interface DemoOptions {
  mode: 'bench' | 'matmul' | 'full';
  config?: Partial<BenchConfig | MatMulConfig>;
  verbose?: boolean;
  outputDir?: string;
}

export class HologramDemo {
  private options: DemoOptions;

  constructor(options: DemoOptions) {
    this.options = options;
  }

  /**
   * Run the complete demo
   */
  async run(): Promise<void> {
    console.log('🚀 HOLOGRAM VIRTUAL INFRA MATMUL DEMO');
    console.log('='.repeat(60));
    console.log('12,288 lattice (48×256) with verifiable streaming matrix multiplication');
    console.log('Target: ≥ 25 Gbit/s sustained throughput with tight latency/jitter');
    console.log('='.repeat(60));

    if (this.options.verbose) {
      console.log(`Mode: ${this.options.mode}`);
      console.log(`Config: ${JSON.stringify(this.options.config, null, 2)}`);
    }

    try {
      switch (this.options.mode) {
        case 'bench':
          await this.runBenchmark();
          break;
        case 'matmul':
          await this.runMatMul();
          break;
        case 'full':
          await this.runFullDemo();
          break;
        default:
          throw new Error(`Unknown mode: ${this.options.mode}`);
      }
    } catch (error) {
      console.error('Demo failed:', error);
      process.exit(1);
    }
  }

  /**
   * Run benchmark mode
   */
  private async runBenchmark(): Promise<void> {
    console.log('\n📊 Running Benchmark Mode');
    console.log('-'.repeat(40));

    const config: BenchConfig = {
      duration: 10,
      lanes: 64,
      payload: 4096,
      batch: 16,
      workers: 4,
      window: 100,
      target: 25,
      ...this.options.config
    };

    const bench = new BenchStep(config);
    const result = await bench.runBenchmark();

    if (result.allGatesPassed) {
      console.log('\n🎉 Benchmark completed successfully - all gates passed!');
      process.exit(0);
    } else {
      console.log('\n💥 Benchmark failed - some gates did not pass');
      process.exit(1);
    }
  }

  /**
   * Run matrix multiplication mode
   */
  private async runMatMul(): Promise<void> {
    console.log('\n🔢 Running Matrix Multiplication Mode');
    console.log('-'.repeat(40));

    const config: MatMulConfig = {
      ...createDefaultMatMulConfig(),
      ...this.options.config
    };

    const matMul = new MatMulStep(config);
    const result = await matMul.runMatMulPipeline();

    if (result.allGatesPassed) {
      console.log('\n🎉 Matrix multiplication completed successfully - all gates passed!');
      console.log(`Matrix stats: ${result.matrixStats.totalBlocks} blocks processed`);
      process.exit(0);
    } else {
      console.log('\n💥 Matrix multiplication failed - some gates did not pass');
      process.exit(1);
    }
  }

  /**
   * Run full demo (benchmark + matmul)
   */
  private async runFullDemo(): Promise<void> {
    console.log('\n🎯 Running Full Demo (Benchmark + Matrix Multiplication)');
    console.log('-'.repeat(40));

    // First run benchmark
    console.log('\n📊 Phase 1: Benchmark');
    const benchConfig: BenchConfig = {
      duration: 5, // Shorter for full demo
      lanes: 64,
      payload: 4096,
      batch: 16,
      workers: 4,
      window: 100,
      target: 25,
      ...this.options.config
    };

    const bench = new BenchStep(benchConfig);
    const benchResult = await bench.runBenchmark();

    if (!benchResult.allGatesPassed) {
      console.log('\n💥 Benchmark phase failed - aborting full demo');
      process.exit(1);
    }

    // Then run matrix multiplication
    console.log('\n🔢 Phase 2: Matrix Multiplication');
    const matMulConfig: MatMulConfig = {
      ...createDefaultMatMulConfig(),
      size: 1024, // Smaller for full demo
      ...this.options.config
    };

    const matMul = new MatMulStep(matMulConfig);
    const matMulResult = await matMul.runMatMulPipeline();

    if (matMulResult.allGatesPassed) {
      console.log('\n🎉 Full demo completed successfully - all gates passed!');
      console.log(`Benchmark: ${benchResult.allGatesPassed ? '✅ PASS' : '❌ FAIL'}`);
      console.log(`Matrix multiplication: ${matMulResult.allGatesPassed ? '✅ PASS' : '❌ FAIL'}`);
      process.exit(0);
    } else {
      console.log('\n💥 Matrix multiplication phase failed');
      process.exit(1);
    }
  }
}

// CLI interface
program
  .name('holomatrix-demo')
  .description('Hologram Virtual Infra MatMul Demo - 12,288 lattice with 25 Gbit/s target')
  .version('1.0.0');

program
  .command('bench')
  .description('Run benchmark mode')
  .option('-d, --duration <seconds>', 'Test duration in seconds', '10')
  .option('-l, --lanes <count>', 'Number of lanes', '64')
  .option('-p, --payload <bytes>', 'Payload size in bytes', '4096')
  .option('-b, --batch <count>', 'Batch size', '16')
  .option('-w, --workers <count>', 'Number of workers', '4')
  .option('-W, --window <ms>', 'Window size in milliseconds', '100')
  .option('-t, --target <gbps>', 'Target throughput in Gbit/s', '25')
  .option('-v, --verbose', 'Verbose output', false)
  .action(async (options) => {
    const demo = new HologramDemo({
      mode: 'bench',
      config: {
        duration: parseInt(options.duration),
        lanes: parseInt(options.lanes),
        payload: parseInt(options.payload),
        batch: parseInt(options.batch),
        workers: parseInt(options.workers),
        window: parseInt(options.window),
        target: parseInt(options.target)
      },
      verbose: options.verbose
    });

    await demo.run();
  });

program
  .command('matmul')
  .description('Run matrix multiplication mode')
  .option('-s, --size <n>', 'Matrix size (side length)', '2048')
  .option('-b, --block <n>', 'Block size', '128')
  .option('-l, --lanes <count>', 'Number of lanes', '64')
  .option('-p, --payload <bytes>', 'Payload size in bytes', '4096')
  .option('-B, --batch <count>', 'Batch size', '16')
  .option('-w, --workers <count>', 'Number of workers', '4')
  .option('-W, --window <ms>', 'Window size in milliseconds', '100')
  .option('-t, --targetGbps <float>', 'Target throughput in Gbit/s', '25')
  .option('-i, --iterations <count>', 'Number of iterations to run', '200')
  .option('-v, --verbose', 'Verbose output', false)
  .action(async (options) => {
    const demo = new HologramDemo({
      mode: 'matmul',
      config: {
        size: parseInt(options.size),
        block: parseInt(options.block),
        lanes: parseInt(options.lanes),
        payload: parseInt(options.payload),
        batch: parseInt(options.batch),
        workers: parseInt(options.workers),
        window: parseInt(options.window),
        targetGbps: parseFloat(options.targetGbps),
        iterations: parseInt(options.iterations)
      },
      verbose: options.verbose
    });

    await demo.run();
  });

program
  .command('full')
  .description('Run full demo (benchmark + matrix multiplication)')
  .option('-d, --duration <seconds>', 'Benchmark duration in seconds', '5')
  .option('-s, --size <n>', 'Matrix size (side length)', '1024')
  .option('-b, --block <n>', 'Block size', '128')
  .option('-l, --lanes <count>', 'Number of lanes', '64')
  .option('-p, --payload <bytes>', 'Payload size in bytes', '4096')
  .option('-B, --batch <count>', 'Batch size', '16')
  .option('-w, --workers <count>', 'Number of workers', '4')
  .option('-W, --window <ms>', 'Window size in milliseconds', '100')
  .option('-t, --target <gbps>', 'Target throughput in Gbit/s', '25')
  .option('-v, --verbose', 'Verbose output', false)
  .action(async (options) => {
    const demo = new HologramDemo({
      mode: 'full',
      config: {
        duration: parseInt(options.duration),
        size: parseInt(options.size),
        block: parseInt(options.block),
        lanes: parseInt(options.lanes),
        payload: parseInt(options.payload),
        batch: parseInt(options.batch),
        workers: parseInt(options.workers),
        window: parseInt(options.window),
        target: parseInt(options.target),
        targetGbps: parseInt(options.target)
      },
      verbose: options.verbose
    });

    await demo.run();
  });

// Default command
program
  .command('*')
  .description('Run default demo (matrix multiplication)')
  .action(async () => {
    const demo = new HologramDemo({
      mode: 'matmul',
      config: createDefaultMatMulConfig(),
      verbose: true
    });

    await demo.run();
  });

// Main execution
if (require.main === module) {
  program.parse();
}

#!/usr/bin/env ts-node

/**
 * CLI for 25G Throughput Benchmark Validation
 * 
 * Usage:
 *   ts-node src/steps/04-bench.ts [options]
 * 
 * Default profile tuned for 25G proof:
 *   duration=10s, lanes=32, payload=4096, batch=16, window=100ms, workers=4
 * 
 * Exit codes:
 *   0: All criteria passed (≥25G, p99≤2ms, window≥99%, loss≤2%)
 *   1: Some criteria failed
 */

import { runLoad, RunArgs } from '../bench/loadgen';
import { printReport, exportToJson } from '../bench/report';
import { writeFileSync, mkdirSync } from 'fs';
// import { join } from 'path'; // Unused for now

interface CliArgs {
  duration: number;
  lanes: number;
  payload: number;
  batch: number;
  window: number;
  workers: number;
  target: number;
  aggregateTo?: number | undefined;
  output?: string | undefined;
  matrix: boolean;
  help: boolean;
}

/**
 * Parse command line arguments
 */
function parseArgs(): CliArgs {
  const args: CliArgs = {
    duration: 10,
    lanes: 32,
    payload: 4096,
    batch: 16,
    window: 100,
    workers: 4,
    target: 25,
    matrix: false,
    help: false,
  };
  
  const argv = process.argv.slice(2);
  
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    
    switch (arg) {
      case '--duration':
        args.duration = parseInt(argv[++i] || '') || args.duration;
        break;
      case '--lanes':
        args.lanes = parseInt(argv[++i] || '') || args.lanes;
        break;
      case '--payload':
        args.payload = parseInt(argv[++i] || '') || args.payload;
        break;
      case '--batch':
        args.batch = parseInt(argv[++i] || '') || args.batch;
        break;
      case '--window':
        args.window = parseInt(argv[++i] || '') || args.window;
        break;
      case '--workers':
        args.workers = parseInt(argv[++i] || '') || args.workers;
        break;
      case '--target':
        args.target = parseInt(argv[++i] || '') || args.target;
        break;
      case '--aggregate-to':
        const aggValue = argv[++i];
        if (aggValue) {
          args.aggregateTo = parseInt(aggValue);
        }
        break;
      case '--output':
        const outputValue = argv[++i];
        if (outputValue) {
          args.output = outputValue;
        }
        break;
      case '--matrix':
        args.matrix = true;
        break;
      case '--help':
      case '-h':
        args.help = true;
        break;
    }
  }
  
  return args;
}

/**
 * Print help message
 */
function printHelp(): void {
  console.log(`
25G Throughput Benchmark for Hologram 12,288-lattice

Usage:
  ts-node src/steps/04-bench.ts [options]

Options:
  --duration <sec>     Test duration in seconds (default: 10)
  --lanes <count>      Number of lanes/columns (default: 32)
  --payload <bytes>    Payload size in bytes (default: 4096)
  --batch <size>       Batch size for sends (default: 16)
  --window <ms>        Window size in milliseconds (default: 100)
  --workers <count>    Number of worker threads (default: 4)
  --target <gbps>      Target throughput in Gb/s (default: 25)
  --aggregate-to <bytes> Aggregate small payloads to this size
  --output <file>      Save results to JSON file
  --matrix             Run matrix sweep to find optimal config
  --help, -h           Show this help message

Environment Variables:
  HOLOGRAM_USE_MOCK    Set to 'false' to use real SDK (default: true)
  MOCK_SPEED_FACTOR    Speed multiplier for mock testing (default: 1)

Examples:
  # Default 25G test
  ts-node src/steps/04-bench.ts

  # Custom test with larger payload
  ts-node src/steps/04-bench.ts --duration 15 --lanes 64 --payload 8192

  # Test with aggregation for small payloads
  ts-node src/steps/04-bench.ts --payload 1024 --aggregate-to 4096

  # Matrix sweep to find best config
  ts-node src/steps/04-bench.ts --matrix

  # Use real SDK
  HOLOGRAM_USE_MOCK=false ts-node src/steps/04-bench.ts

Pass/Fail Criteria:
  ✅ Throughput ≥ Target Gb/s
  ✅ P99 Latency ≤ 2.0ms
  ✅ Window Efficiency ≥ 99%
  ✅ Loss Rate ≤ 2%

Exit Codes:
  0: All criteria passed
  1: Some criteria failed
`);
}

/**
 * Run matrix sweep to find optimal configuration
 */
async function runMatrixSweep(): Promise<void> {
  console.log('🔍 Running matrix sweep to find optimal configuration...\n');
  
  const payloads = [1024, 2048, 4096, 8192];
  const lanes = [8, 16, 32, 64];
  const batches = [1, 8, 16, 32];
  const aggregateOptions = [undefined, 4096];
  
  const results: Array<{
    config: RunArgs;
    stats: any;
    passed: boolean;
  }> = [];
  
  let testCount = 0;
  const totalTests = payloads.length * lanes.length * batches.length * aggregateOptions.length;
  
  for (const payload of payloads) {
    for (const lane of lanes) {
      for (const batch of batches) {
        for (const aggregateTo of aggregateOptions) {
          testCount++;
          
          // Skip aggregation if payload is already large enough
          if (aggregateTo && payload >= aggregateTo) {
            continue;
          }
          
          console.log(`[${testCount}/${totalTests}] Testing: payload=${payload}B, lanes=${lane}, batch=${batch}, aggregate=${aggregateTo || 'none'}`);
          
          const config: RunArgs = {
            durationSec: 5, // Shorter duration for matrix
            lanes: lane,
            payloadBytes: payload,
            targetGbps: 25,
            batch: batch,
            windowMs: 100,
            workers: Math.min(4, lane / 8), // Scale workers with lanes
            aggregateTo,
            budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
          };
          
          try {
            const stats = await runLoad(config);
            const passed = stats.gbps >= 25 && 
                          stats.p99latencyMs <= 2.0 && 
                          (stats.settleClosed / stats.settleTotal) >= 0.99 && 
                          (stats.rejected / stats.sent) <= 0.02;
            
            results.push({ config, stats, passed });
            
            const status = passed ? '✅ PASS' : '❌ FAIL';
            console.log(`  ${status} - ${stats.gbps.toFixed(1)} Gb/s, p99: ${stats.p99latencyMs.toFixed(2)}ms\n`);
            
          } catch (error) {
            console.log(`  ❌ ERROR - ${error}\n`);
          }
        }
      }
    }
  }
  
  // Find best configuration
  const passingResults = results.filter(r => r.passed);
  if (passingResults.length > 0) {
    const best = passingResults.reduce((best, current) => 
      current.stats.gbps > best.stats.gbps ? current : best
    );
    
    console.log('🏆 Best Configuration Found:');
    console.log(`  Payload: ${best.config.payloadBytes}B`);
    console.log(`  Lanes: ${best.config.lanes}`);
    console.log(`  Batch: ${best.config.batch}`);
    console.log(`  Aggregate: ${best.config.aggregateTo || 'none'}`);
    console.log(`  Throughput: ${best.stats.gbps.toFixed(1)} Gb/s`);
    console.log(`  P99 Latency: ${best.stats.p99latencyMs.toFixed(2)}ms`);
    console.log();
  } else {
    console.log('❌ No configuration achieved 25G target\n');
  }
}

/**
 * Main CLI function
 */
async function main(): Promise<void> {
  const args = parseArgs();
  
  if (args.help) {
    printHelp();
    return;
  }
  
  // Check environment
  const useMock = process.env['HOLOGRAM_USE_MOCK'] !== 'false';
  console.log(`🔧 Using ${useMock ? 'MOCK' : 'REAL'} Hologram SDK`);
  
  if (args.matrix) {
    await runMatrixSweep();
    return;
  }
  
  // Set aggregation if payload is small
  if (!args.aggregateTo && args.payload < 4096) {
    args.aggregateTo = 4096;
  }
  
  // Build run configuration
  const runArgs: RunArgs = {
    durationSec: args.duration,
    lanes: args.lanes,
    payloadBytes: args.payload,
    targetGbps: args.target,
    batch: args.batch,
    windowMs: args.window,
    workers: args.workers,
    aggregateTo: args.aggregateTo,
    budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
  };
  
  try {
    // Run benchmark
    const stats = await runLoad(runArgs);
    
    // Print report
    const passed = printReport(stats, runArgs, {
      showLaneUtil: true,
      showDetailed: true,
      colorOutput: true,
    });
    
    // Save results if requested
    if (args.output) {
      const results = exportToJson(stats, runArgs);
      writeFileSync(args.output, JSON.stringify(results, null, 2));
      console.log(`📁 Results saved to: ${args.output}`);
    }
    
    // Auto-save to bench-results directory
    try {
      mkdirSync('./bench-results', { recursive: true });
      const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
      const autoOutput = `./bench-results/${timestamp}.json`;
      const results = exportToJson(stats, runArgs);
      writeFileSync(autoOutput, JSON.stringify(results, null, 2));
      console.log(`📁 Auto-saved to: ${autoOutput}`);
    } catch (error) {
      // Ignore auto-save errors
    }
    
    // Exit with appropriate code
    process.exit(passed ? 0 : 1);
    
  } catch (error) {
    console.error('💥 Benchmark failed:', error);
    process.exit(1);
  }
}

// Run if called directly
if (require.main === module) {
  main().catch(error => {
    console.error('💥 Fatal error:', error);
    process.exit(1);
  });
}


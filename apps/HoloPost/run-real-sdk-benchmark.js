#!/usr/bin/env node

/**
 * Real SDK 25G Throughput Benchmark Runner
 * 
 * This script runs comprehensive benchmarks using the actual Hologram SDK
 * to validate 25G/second throughput performance.
 * 
 * Usage:
 *   node run-real-sdk-benchmark.js [options]
 * 
 * Options:
 *   --duration <sec>     Test duration (default: 15)
 *   --lanes <count>      Number of lanes (default: 64)
 *   --payload <bytes>    Payload size (default: 4096)
 *   --workers <count>    Worker threads (default: 8)
 *   --target <gbps>      Target throughput (default: 25)
 *   --comprehensive      Run comprehensive test suite
 *   --stress             Run stress tests
 *   --compare            Compare with mock SDK
 */

const { spawn } = require('child_process');
const path = require('path');

// Configuration
const config = {
  duration: 15,
  lanes: 64,
  payload: 4096,
  workers: 8,
  target: 25,
  comprehensive: false,
  stress: false,
  compare: false
};

// Parse command line arguments
function parseArgs() {
  const args = process.argv.slice(2);
  
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    
    switch (arg) {
      case '--duration':
        config.duration = parseInt(args[++i]) || config.duration;
        break;
      case '--lanes':
        config.lanes = parseInt(args[++i]) || config.lanes;
        break;
      case '--payload':
        config.payload = parseInt(args[++i]) || config.payload;
        break;
      case '--workers':
        config.workers = parseInt(args[++i]) || config.workers;
        break;
      case '--target':
        config.target = parseInt(args[++i]) || config.target;
        break;
      case '--comprehensive':
        config.comprehensive = true;
        break;
      case '--stress':
        config.stress = true;
        break;
      case '--compare':
        config.compare = true;
        break;
      case '--help':
      case '-h':
        printHelp();
        process.exit(0);
        break;
    }
  }
}

function printHelp() {
  console.log(`
Real SDK 25G Throughput Benchmark Runner

Usage:
  node run-real-sdk-benchmark.js [options]

Options:
  --duration <sec>     Test duration in seconds (default: 15)
  --lanes <count>      Number of transport lanes (default: 64)
  --payload <bytes>    Payload size in bytes (default: 4096)
  --workers <count>    Number of worker threads (default: 8)
  --target <gbps>      Target throughput in Gb/s (default: 25)
  --comprehensive      Run comprehensive test suite
  --stress             Run stress tests
  --compare            Compare with mock SDK
  --help, -h           Show this help message

Examples:
  # Basic 25G benchmark
  node run-real-sdk-benchmark.js

  # High-performance test
  node run-real-sdk-benchmark.js --duration 30 --lanes 128 --workers 16

  # Comprehensive test suite
  node run-real-sdk-benchmark.js --comprehensive

  # Stress test
  node run-real-sdk-benchmark.js --stress --duration 60

  # Compare with mock
  node run-real-sdk-benchmark.js --compare
`);
}

// Run a command and return a promise
function runCommand(command, args, env = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, {
      stdio: 'inherit',
      env: { ...process.env, ...env },
      cwd: path.join(__dirname)
    });

    child.on('close', (code) => {
      if (code === 0) {
        resolve(code);
      } else {
        reject(new Error(`Command failed with code ${code}`));
      }
    });

    child.on('error', (error) => {
      reject(error);
    });
  });
}

// Run Jest tests
async function runJestTests(testPattern, env = {}) {
  console.log(`\n🧪 Running Jest tests: ${testPattern}`);
  console.log('='.repeat(60));
  
  try {
    await runCommand('npx', ['jest', testPattern, '--verbose', '--detectOpenHandles'], env);
    console.log('✅ Jest tests completed successfully');
  } catch (error) {
    console.error('❌ Jest tests failed:', error.message);
    throw error;
  }
}

// Run benchmark CLI
async function runBenchmarkCLI(args, env = {}) {
  console.log(`\n📊 Running benchmark CLI with args: ${args.join(' ')}`);
  console.log('='.repeat(60));
  
  try {
    await runCommand('npx', ['ts-node', 'src/steps/04-bench.ts', ...args], env);
    console.log('✅ Benchmark CLI completed successfully');
  } catch (error) {
    console.error('❌ Benchmark CLI failed:', error.message);
    throw error;
  }
}

// Run optimized throughput test
async function runOptimizedTest(env = {}) {
  console.log('\n🚀 Running optimized throughput test');
  console.log('='.repeat(60));
  
  try {
    await runCommand('npx', ['ts-node', 'src/optimized-throughput-test.ts'], env);
    console.log('✅ Optimized throughput test completed successfully');
  } catch (error) {
    console.error('❌ Optimized throughput test failed:', error.message);
    throw error;
  }
}

// Main benchmark runner
async function runBenchmarks() {
  console.log('🚀 REAL SDK 25G THROUGHPUT BENCHMARK');
  console.log('='.repeat(80));
  console.log(`📋 Configuration:`);
  console.log(`   Duration: ${config.duration}s`);
  console.log(`   Lanes: ${config.lanes}`);
  console.log(`   Payload: ${config.payload}B`);
  console.log(`   Workers: ${config.workers}`);
  console.log(`   Target: ${config.target} Gb/s`);
  console.log(`   Comprehensive: ${config.comprehensive}`);
  console.log(`   Stress: ${config.stress}`);
  console.log(`   Compare: ${config.compare}`);
  console.log('='.repeat(80));

  const realSDKEnv = { HOLOGRAM_USE_MOCK: 'false' };
  const mockSDKEnv = { HOLOGRAM_USE_MOCK: 'true', MOCK_SPEED_FACTOR: '1' };

  try {
    // 1. Run real SDK benchmark tests
    console.log('\n🔧 PHASE 1: Real SDK Integration Tests');
    await runJestTests('tests/real-sdk-benchmark.spec.ts', realSDKEnv);

    // 2. Run basic 25G benchmark with real SDK
    console.log('\n📊 PHASE 2: Basic 25G Benchmark (Real SDK)');
    const benchmarkArgs = [
      '--duration', config.duration.toString(),
      '--lanes', config.lanes.toString(),
      '--payload', config.payload.toString(),
      '--workers', config.workers.toString(),
      '--target', config.target.toString(),
      '--batch', '32',
      '--window', '100'
    ];
    await runBenchmarkCLI(benchmarkArgs, realSDKEnv);

    // 3. Run optimized throughput test
    console.log('\n🚀 PHASE 3: Optimized Throughput Test');
    await runOptimizedTest(realSDKEnv);

    // 4. Comprehensive tests if requested
    if (config.comprehensive) {
      console.log('\n🔍 PHASE 4: Comprehensive Test Suite');
      
      // Test different payload sizes
      const payloadSizes = [1024, 2048, 4096, 8192, 16384];
      for (const payloadSize of payloadSizes) {
        console.log(`\n📦 Testing payload size: ${payloadSize}B`);
        await runBenchmarkCLI([
          '--duration', '5',
          '--lanes', '32',
          '--payload', payloadSize.toString(),
          '--workers', '4',
          '--target', '10',
          '--batch', '16'
        ], realSDKEnv);
      }

      // Test different lane counts
      const laneCounts = [16, 32, 64, 128];
      for (const laneCount of laneCounts) {
        console.log(`\n🛤️  Testing lane count: ${laneCount}`);
        await runBenchmarkCLI([
          '--duration', '5',
          '--lanes', laneCount.toString(),
          '--payload', '4096',
          '--workers', Math.min(8, laneCount / 8).toString(),
          '--target', '15',
          '--batch', '16'
        ], realSDKEnv);
      }
    }

    // 5. Stress tests if requested
    if (config.stress) {
      console.log('\n💪 PHASE 5: Stress Tests');
      
      // High concurrency stress test
      console.log('\n🔥 High Concurrency Stress Test');
      await runBenchmarkCLI([
        '--duration', '20',
        '--lanes', '128',
        '--payload', '8192',
        '--workers', '16',
        '--target', '50',
        '--batch', '64',
        '--window', '50'
      ], realSDKEnv);

      // Memory pressure test
      console.log('\n🧠 Memory Pressure Test');
      await runBenchmarkCLI([
        '--duration', '15',
        '--lanes', '64',
        '--payload', '16384',
        '--workers', '8',
        '--target', '30',
        '--batch', '32'
      ], realSDKEnv);
    }

    // 6. Comparison with mock SDK if requested
    if (config.compare) {
      console.log('\n⚖️  PHASE 6: Mock vs Real SDK Comparison');
      
      // Run same test with mock SDK
      console.log('\n🎭 Mock SDK Benchmark');
      await runBenchmarkCLI(benchmarkArgs, mockSDKEnv);
      
      // Run same test with real SDK again for comparison
      console.log('\n🔧 Real SDK Benchmark (for comparison)');
      await runBenchmarkCLI(benchmarkArgs, realSDKEnv);
    }

    console.log('\n🎉 ALL BENCHMARKS COMPLETED SUCCESSFULLY!');
    console.log('='.repeat(80));
    console.log('📊 Summary:');
    console.log('   ✅ Real SDK integration validated');
    console.log('   ✅ 25G throughput benchmark completed');
    console.log('   ✅ Optimized throughput test passed');
    if (config.comprehensive) console.log('   ✅ Comprehensive test suite completed');
    if (config.stress) console.log('   ✅ Stress tests completed');
    if (config.compare) console.log('   ✅ Mock vs Real SDK comparison completed');
    console.log('\n💡 Check the output above for detailed performance metrics.');

  } catch (error) {
    console.error('\n💥 BENCHMARK FAILED:', error.message);
    console.log('\n🔍 Troubleshooting:');
    console.log('   • Ensure all dependencies are installed: npm install');
    console.log('   • Check that the real SDK is properly configured');
    console.log('   • Verify network connectivity for SDK operations');
    console.log('   • Check system resources (CPU, memory, network)');
    process.exit(1);
  }
}

// Parse arguments and run benchmarks
parseArgs();
runBenchmarks().catch(error => {
  console.error('💥 Fatal error:', error);
  process.exit(1);
});

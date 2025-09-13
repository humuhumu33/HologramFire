#!/usr/bin/env node

/**
 * Optimized 25G Benchmark Runner
 * 
 * This script runs the optimized benchmark to achieve 25G throughput target
 * by implementing the key optimizations identified in the performance analysis.
 */

const { runOptimized25GBenchmark } = require('./dist/optimized-25g-benchmark');

async function main() {
  console.log('🚀 Starting Optimized 25G Throughput Benchmark...');
  console.log('Target: 25 Gb/s (current: 13.3 Gb/s - 53% of target)');
  console.log('Optimizations:');
  console.log('  - 512 lanes (vs 32 current)');
  console.log('  - 128 workers (vs 4 current)');
  console.log('  - 64KB payloads (vs 4KB current)');
  console.log('  - Hardware acceleration');
  console.log('  - Advanced compression');
  console.log('  - Optimized algorithms');
  console.log('');
  
  try {
    await runOptimized25GBenchmark();
    console.log('\n✅ Benchmark completed successfully!');
  } catch (error) {
    console.error('\n❌ Benchmark failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main().catch(console.error);
}

module.exports = { main };

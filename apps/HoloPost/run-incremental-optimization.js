#!/usr/bin/env node

/**
 * Run Incremental Throughput Optimization
 * 
 * This script runs the incremental optimization process to gradually
 * improve throughput from 839 MB/s to 25 GB/s through 6 phases.
 */

// Set environment variables for optimization
process.env.HOLOGRAM_USE_MOCK = 'false';
process.env.HOLOGRAM_USE_ENHANCED = 'true';

// Performance optimization settings
process.env.UV_THREADPOOL_SIZE = '64';
process.env.NODE_OPTIONS = '--max-old-space-size=8192 --expose-gc';

// Import and run the incremental optimization
const { runIncrementalOptimization } = require('./dist/incremental-optimization.js');

async function main() {
  try {
    console.log('🚀 Starting Incremental Throughput Optimization');
    console.log('='.repeat(80));
    console.log('📋 This will run 6 phases to gradually improve throughput:');
    console.log('   Phase 1: Basic Parallel Processing (2 GB/s target)');
    console.log('   Phase 2: Enhanced Concurrency (5 GB/s target)');
    console.log('   Phase 3: Network Optimization (10 GB/s target)');
    console.log('   Phase 4: Hardware Acceleration (15 GB/s target)');
    console.log('   Phase 5: GPU Acceleration (20 GB/s target)');
    console.log('   Phase 6: Target Achievement (25 GB/s target)');
    console.log('='.repeat(80));
    
    await runIncrementalOptimization();
    
    console.log('\n🎉 Incremental optimization completed!');
    console.log('📊 Check the results above to see the progress toward 25 GB/s target.');
    
  } catch (error) {
    console.error('\n❌ Incremental optimization failed:', error);
    process.exit(1);
  }
}

main();

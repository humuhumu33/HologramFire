#!/usr/bin/env node

/**
 * Run Enhanced Throughput Test for 25 GB/s Target
 * 
 * This script runs the optimized throughput test with enhanced real SDK
 * to achieve the 25 GB/s performance target.
 */

// Set environment variables for enhanced performance
process.env.HOLOGRAM_USE_MOCK = 'false';
process.env.HOLOGRAM_USE_ENHANCED = 'true';

// Performance optimization settings
process.env.UV_THREADPOOL_SIZE = '64';
process.env.NODE_OPTIONS = '--max-old-space-size=8192 --expose-gc';

// Import and run the optimized throughput test
const { runOptimizedThroughputTest } = require('./dist/optimized-throughput-test.js');

async function main() {
  try {
    console.log('🚀 Running Enhanced Throughput Test for 25 GB/s Target');
    console.log('='.repeat(80));
    console.log('🔧 Configuration:');
    console.log('   • Enhanced Real SDK: Enabled');
    console.log('   • Worker Threads: 64');
    console.log('   • Max Concurrency: 1000');
    console.log('   • Network Lanes: 512');
    console.log('   • Compression: Enabled');
    console.log('   • Zero-Copy: Enabled');
    console.log('   • RDMA: Enabled');
    console.log('   • GPU Acceleration: Enabled');
    console.log('='.repeat(80));
    
    await runOptimizedThroughputTest();
    
    console.log('\n🎉 Enhanced throughput test completed successfully!');
    console.log('📊 Check the results above to see if 25 GB/s target was achieved.');
    
  } catch (error) {
    console.error('\n❌ Enhanced throughput test failed:', error);
    process.exit(1);
  }
}

main();

#!/usr/bin/env node

/**
 * Run throughput test with real SDK implementation
 */

// Set environment variable to use real SDK
process.env.HOLOGRAM_USE_MOCK = 'false';

// Import and run the throughput test
const { runThroughputTest } = require('./dist/throughput-test.js');

async function main() {
  try {
    console.log('🚀 Running throughput test with REAL SDK implementation');
    console.log('='.repeat(60));
    await runThroughputTest();
    console.log('\n🎉 Throughput test completed successfully!');
  } catch (error) {
    console.error('\n❌ Throughput test failed:', error);
    process.exit(1);
  }
}

main();

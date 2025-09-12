#!/usr/bin/env node

/**
 * Proof Chain Example Runner
 * 
 * This script runs the comprehensive data transformation proof chain example,
 * demonstrating full provenance tracking and verification.
 */

const { runProofChainExample } = require('./proof-chain-example');

console.log('🚀 Starting Hologram Proof Chain Example');
console.log('==========================================');
console.log('');

// Run the example
runProofChainExample()
  .then(() => {
    console.log('');
    console.log('✅ Example completed successfully!');
    console.log('');
    console.log('📚 For more information, see:');
    console.log('   - examples/proof-chain-visualization.md');
    console.log('   - src/proof-chain/README.md');
    console.log('');
    process.exit(0);
  })
  .catch((error) => {
    console.error('');
    console.error('❌ Example failed:', error.message);
    console.error('');
    console.error('Stack trace:');
    console.error(error.stack);
    console.error('');
    process.exit(1);
  });

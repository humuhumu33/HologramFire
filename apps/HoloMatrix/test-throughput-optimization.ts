/**
 * Test script for throughput optimization
 * Quick test to verify the optimizations work
 */

import { DoubleBufferedMatMul } from './src/steps/05-matmul-throughput-optimized';
import type { MatMulConfig } from './src/types';

async function testThroughputOptimization() {
  console.log('🧪 Testing Throughput Optimization');
  console.log('='.repeat(50));

  // Test configuration - smaller for quick testing
  const config: MatMulConfig = {
    size: 1024,        // Smaller matrix for quick test
    block: 64,         // Smaller blocks
    lanes: 32,         // Fewer lanes
    payload: 4096,     // Smaller payload
    batch: 128,        // Moderate batch
    workers: 4,        // Fewer workers
    window: 100,       // Standard window
    targetGbps: 0.5,   // Lower target for testing
    iterations: 10     // Few iterations for quick test
  };

  console.log('Configuration:');
  console.log(`  Matrix: ${config.size}×${config.size}`);
  console.log(`  Blocks: ${config.block}×${config.block}`);
  console.log(`  Lanes: ${config.lanes}`);
  console.log(`  Workers: ${config.workers}`);
  console.log(`  Iterations: ${config.iterations}`);
  console.log(`  Target: ${config.targetGbps} Gbit/s`);
  console.log('='.repeat(50));

  try {
    const matMul = new DoubleBufferedMatMul(config);
    const result = await matMul.runOptimizedPipeline();

    console.log('\n📊 TEST RESULTS');
    console.log('='.repeat(30));
    console.log(`Success: ${result.success ? '✅ PASS' : '❌ FAIL'}`);
    console.log(`All Gates Passed: ${result.allGatesPassed ? '✅ PASS' : '❌ FAIL'}`);
    console.log(`Throughput: ${result.throughputStats.gbps.toFixed(3)} Gbit/s`);
    console.log(`Target: ${config.targetGbps} Gbit/s`);
    console.log(`Achievement: ${((result.throughputStats.gbps / config.targetGbps) * 100).toFixed(1)}%`);

    if (result.success) {
      console.log('\n🎉 OPTIMIZATION TEST PASSED!');
      console.log('The throughput optimizations are working correctly.');
    } else {
      console.log('\n⚠️  OPTIMIZATION TEST FAILED');
      console.log('The throughput is below the target. This may be expected for the test configuration.');
    }

    return result.success;

  } catch (error) {
    console.error('\n💥 TEST FAILED WITH ERROR:');
    console.error(error);
    return false;
  }
}

// Run the test
if (require.main === module) {
  testThroughputOptimization()
    .then(success => {
      process.exit(success ? 0 : 1);
    })
    .catch(error => {
      console.error('Test runner failed:', error);
      process.exit(1);
    });
}

export { testThroughputOptimization };

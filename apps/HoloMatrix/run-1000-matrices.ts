/**
 * Run 1000 Matrix Computations Test
 * Custom script to test HoloMatrix with 1000 matrix multiplication operations
 */

import { MatMulStep } from './src/steps/05-matmul';
import { createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';

interface TestResult {
  iteration: number;
  success: boolean;
  allGatesPassed: boolean;
  duration: number;
  throughput: number;
  transportP99: number;
  storageP99: number;
  computeP99: number;
  e2eP99: number;
  windowClosure: number;
  rejectRate: number;
  totalBlocks: number;
}

class Matrix1000Test {
  private config: MatMulConfig;
  private results: TestResult[] = [];

  constructor() {
    // Configure for 1000 computations with performance gates
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 2048,       // Required: 2048x2048 matrix
      block: 128,       // Required: 128x128 blocks
      lanes: 64,        // Transport parameters for 25 Gbit/s
      payload: 4096,    // Transport parameters for 25 Gbit/s
      batch: 16,        // Transport parameters for 25 Gbit/s
      workers: 4,       // Transport parameters for 25 Gbit/s
      window: 100,      // Transport parameters for 25 Gbit/s
      targetGbps: 25.0  // Required: 25 Gbit/s target
    };
  }

  async run1000Matrices(): Promise<void> {
    console.log('🚀 HOLOMATRIX 1000 MATRIX COMPUTATIONS TEST');
    console.log('='.repeat(60));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Iterations: 1000`);
    console.log('='.repeat(60));

    const startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;

    for (let i = 1; i <= 1000; i++) {
      try {
        console.log(`\n📊 Running iteration ${i}/1000...`);
        
        const iterationStart = Date.now();
        const matMul = new MatMulStep(this.config);
        const result = await matMul.runMatMulPipeline();
        const duration = Date.now() - iterationStart;

        const testResult: TestResult = {
          iteration: i,
          success: result.success,
          allGatesPassed: result.allGatesPassed,
          duration,
          throughput: result.metrics.throughputGbps,
          transportP99: result.metrics.transport.p99Ms,
          storageP99: result.metrics.storage.p99Ms,
          computeP99: result.metrics.compute.p99Ms,
          e2eP99: result.metrics.e2e.p99Ms,
          windowClosure: (result.metrics.transport.windowsClosed / result.metrics.transport.windowsTotal) * 100,
          rejectRate: (result.metrics.transport.rejects / result.metrics.transport.framesSent) * 100,
          totalBlocks: result.matrixStats.totalBlocks
        };

        this.results.push(testResult);

        if (result.success) {
          successCount++;
        }
        if (result.allGatesPassed) {
          gatesPassedCount++;
        }

        // Progress reporting every 50 iterations
        if (i % 50 === 0) {
          const elapsed = (Date.now() - startTime) / 1000;
          const avgTimePerIteration = elapsed / i;
          const estimatedRemaining = (1000 - i) * avgTimePerIteration;
          
          console.log(`\n📈 Progress Report (${i}/1000):`);
          console.log(`  Success rate: ${(successCount / i * 100).toFixed(1)}%`);
          console.log(`  Gates passed: ${(gatesPassedCount / i * 100).toFixed(1)}%`);
          console.log(`  Avg time per iteration: ${avgTimePerIteration.toFixed(2)}s`);
          console.log(`  Estimated remaining: ${(estimatedRemaining / 60).toFixed(1)} minutes`);
        }

        // Brief pause to prevent overwhelming the system
        if (i % 100 === 0) {
          console.log('  ⏸️  Brief pause...');
          await new Promise(resolve => setTimeout(resolve, 1000));
        }

      } catch (error) {
        console.error(`❌ Iteration ${i} failed:`, error);
        
        const testResult: TestResult = {
          iteration: i,
          success: false,
          allGatesPassed: false,
          duration: 0,
          throughput: 0,
          transportP99: 0,
          storageP99: 0,
          computeP99: 0,
          e2eP99: 0,
          windowClosure: 0,
          rejectRate: 0,
          totalBlocks: 0
        };
        
        this.results.push(testResult);
      }
    }

    const totalTime = (Date.now() - startTime) / 1000;
    await this.generateFinalReport(totalTime, successCount, gatesPassedCount);
  }

  private async generateFinalReport(totalTime: number, successCount: number, gatesPassedCount: number): Promise<void> {
    console.log('\n🎯 FINAL TEST RESULTS');
    console.log('='.repeat(60));
    
    // Overall statistics
    console.log(`Total iterations: 1000`);
    console.log(`Successful iterations: ${successCount} (${(successCount / 1000 * 100).toFixed(1)}%)`);
    console.log(`Gates passed iterations: ${gatesPassedCount} (${(gatesPassedCount / 1000 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per iteration: ${(totalTime / 1000).toFixed(2)} seconds`);

    // Performance statistics
    const successfulResults = this.results.filter(r => r.success);
    if (successfulResults.length > 0) {
      const avgThroughput = successfulResults.reduce((sum, r) => sum + r.throughput, 0) / successfulResults.length;
      const avgTransportP99 = successfulResults.reduce((sum, r) => sum + r.transportP99, 0) / successfulResults.length;
      const avgStorageP99 = successfulResults.reduce((sum, r) => sum + r.storageP99, 0) / successfulResults.length;
      const avgComputeP99 = successfulResults.reduce((sum, r) => sum + r.computeP99, 0) / successfulResults.length;
      const avgE2eP99 = successfulResults.reduce((sum, r) => sum + r.e2eP99, 0) / successfulResults.length;
      const avgWindowClosure = successfulResults.reduce((sum, r) => sum + r.windowClosure, 0) / successfulResults.length;
      const avgRejectRate = successfulResults.reduce((sum, r) => sum + r.rejectRate, 0) / successfulResults.length;

      console.log('\n📊 Performance Averages (successful iterations):');
      console.log(`  Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Transport p99: ${avgTransportP99.toFixed(2)} ms`);
      console.log(`  Storage p99: ${avgStorageP99.toFixed(2)} ms`);
      console.log(`  Compute p99: ${avgComputeP99.toFixed(2)} ms`);
      console.log(`  E2E p99: ${avgE2eP99.toFixed(2)} ms`);
      console.log(`  Window closure: ${avgWindowClosure.toFixed(2)}%`);
      console.log(`  Reject rate: ${avgRejectRate.toFixed(2)}%`);
    }

    // Gate analysis
    console.log('\n🚪 Gate Analysis:');
    const gateResults = this.results.filter(r => r.success).map(r => r.allGatesPassed);
    const gatesPassedRate = gateResults.length > 0 ? (gateResults.filter(Boolean).length / gateResults.length * 100) : 0;
    console.log(`  Overall gates passed rate: ${gatesPassedRate.toFixed(1)}%`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/1000-matrices-test-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        totalIterations: 1000,
        successfulIterations: successCount,
        gatesPassedIterations: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerIteration: totalTime / 1000
      },
      performance: successfulResults.length > 0 ? {
        averageThroughput: successfulResults.reduce((sum, r) => sum + r.throughput, 0) / successfulResults.length,
        averageTransportP99: successfulResults.reduce((sum, r) => sum + r.transportP99, 0) / successfulResults.length,
        averageStorageP99: successfulResults.reduce((sum, r) => sum + r.storageP99, 0) / successfulResults.length,
        averageComputeP99: successfulResults.reduce((sum, r) => sum + r.computeP99, 0) / successfulResults.length,
        averageE2eP99: successfulResults.reduce((sum, r) => sum + r.e2eP99, 0) / successfulResults.length,
        averageWindowClosure: successfulResults.reduce((sum, r) => sum + r.windowClosure, 0) / successfulResults.length,
        averageRejectRate: successfulResults.reduce((sum, r) => sum + r.rejectRate, 0) / successfulResults.length
      } : null,
      detailedResults: this.results
    };

    fs.writeFileSync(resultsFile, JSON.stringify(reportData, null, 2));
    console.log(`\n💾 Detailed results saved to: ${resultsFile}`);

    // Final verdict
    console.log('\n🏁 TEST VERDICT:');
    if (successCount >= 950 && gatesPassedCount >= 900) {
      console.log('✅ EXCELLENT: Test passed with high success and gates passed rates');
    } else if (successCount >= 800 && gatesPassedCount >= 700) {
      console.log('✅ GOOD: Test passed with acceptable success and gates passed rates');
    } else if (successCount >= 600) {
      console.log('⚠️  MARGINAL: Test completed but with concerning failure rates');
    } else {
      console.log('❌ POOR: Test failed with high failure rates');
    }
  }
}

// Main execution
async function main() {
  const test = new Matrix1000Test();
  
  try {
    await test.run1000Matrices();
    console.log('\n🎉 1000 matrix computations test completed!');
  } catch (error) {
    console.error('❌ Test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

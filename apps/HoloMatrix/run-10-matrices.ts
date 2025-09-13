/**
 * Run 10 Matrix Computations Test
 * Simplified test to demonstrate HoloMatrix functionality
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

class Matrix10Test {
  private config: MatMulConfig;
  private results: TestResult[] = [];

  constructor() {
    // Configure for smaller matrices for faster testing
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 256,        // Smaller matrix size for faster computation
      block: 32,        // Smaller block size
      lanes: 16,        // Fewer lanes
      payload: 1024,    // Smaller payload
      batch: 4,         // Smaller batch
      workers: 2,       // Fewer workers
      window: 25,       // Smaller window
      targetGbps: 5.0   // Lower target for testing
    };
  }

  async run10Matrices(): Promise<void> {
    console.log('🚀 HOLOMATRIX 10 MATRIX COMPUTATIONS TEST');
    console.log('='.repeat(60));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Iterations: 10`);
    console.log('='.repeat(60));

    const startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;

    for (let i = 1; i <= 10; i++) {
      try {
        console.log(`\n📊 Running iteration ${i}/10...`);
        
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

        console.log(`  ✅ Iteration ${i} completed in ${(duration / 1000).toFixed(2)}s`);
        console.log(`  📈 Throughput: ${result.metrics.throughputGbps.toFixed(2)} Gbit/s`);
        console.log(`  🚪 Gates passed: ${result.allGatesPassed ? 'YES' : 'NO'}`);

        // Brief pause between iterations
        if (i < 10) {
          await new Promise(resolve => setTimeout(resolve, 500));
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
    console.log(`Total iterations: 10`);
    console.log(`Successful iterations: ${successCount} (${(successCount / 10 * 100).toFixed(1)}%)`);
    console.log(`Gates passed iterations: ${gatesPassedCount} (${(gatesPassedCount / 10 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per iteration: ${(totalTime / 10).toFixed(2)} seconds`);

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
    const resultsFile = `${resultsDir}/10-matrices-test-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        totalIterations: 10,
        successfulIterations: successCount,
        gatesPassedIterations: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerIteration: totalTime / 10
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
    if (successCount >= 9 && gatesPassedCount >= 8) {
      console.log('✅ EXCELLENT: Test passed with high success and gates passed rates');
    } else if (successCount >= 7 && gatesPassedCount >= 6) {
      console.log('✅ GOOD: Test passed with acceptable success and gates passed rates');
    } else if (successCount >= 5) {
      console.log('⚠️  MARGINAL: Test completed but with concerning failure rates');
    } else {
      console.log('❌ POOR: Test failed with high failure rates');
    }
  }
}

// Main execution
async function main() {
  const test = new Matrix10Test();
  
  try {
    await test.run10Matrices();
    console.log('\n🎉 10 matrix computations test completed!');
  } catch (error) {
    console.error('❌ Test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

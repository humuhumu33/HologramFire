/**
 * Run 8192×8192 Matrix Multiplication Test
 * Custom script to test HoloMatrix with large 8192×8192 matrix multiplication operations
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
  matrixSize: number;
  blockSize: number;
}

class Matrix8192Test {
  private config: MatMulConfig;
  private results: TestResult[] = [];

  constructor() {
    // Configure for 8192×8192 matrices with optimized parameters
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 8192,       // 8192×8192 matrix
      block: 256,       // Larger blocks for efficiency (256×256)
      lanes: 512,       // Maximum lanes for highest throughput (increased from 128)
      payload: 16384,   // Larger payload size (increased from 8192)
      batch: 64,        // Larger batch size (increased from 32)
      workers: 32,      // More workers for parallel processing (increased from 8)
      window: 100,      // Optimized window for batching (reduced from 200)
      targetGbps: 50.0  // Higher target for large matrices
    };
  }

  async run8192Matrices(): Promise<void> {
    console.log('🚀 HOLOMATRIX 8192×8192 MATRIX MULTIPLICATION TEST');
    console.log('='.repeat(70));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Lanes: ${this.config.lanes}`);
    console.log(`  Workers: ${this.config.workers}`);
    console.log(`  Payload: ${this.config.payload}B`);
    console.log(`  Batch: ${this.config.batch}`);
    console.log('='.repeat(70));

    const startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;

    // Calculate expected blocks
    const blockCount = Math.ceil(this.config.size / this.config.block);
    const totalBlocks = blockCount * blockCount * 2; // A and B matrices
    console.log(`\n📊 Expected blocks: ${totalBlocks} (${blockCount}×${blockCount} per matrix)`);
    console.log(`📊 Block data size: ${this.config.block * this.config.block * 2} bytes per block`);
    console.log(`📊 Total data size: ~${(totalBlocks * this.config.block * this.config.block * 2 / 1024 / 1024).toFixed(1)} MB`);

    try {
      console.log(`\n📊 Running 8192×8192 matrix multiplication...`);
      
      const iterationStart = Date.now();
      const matMul = new MatMulStep(this.config);
      const result = await matMul.runMatMulPipeline();
      const duration = Date.now() - iterationStart;

      const testResult: TestResult = {
        iteration: 1,
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
        totalBlocks: result.matrixStats.totalBlocks,
        matrixSize: this.config.size,
        blockSize: this.config.block
      };

      this.results.push(testResult);

      if (result.success) {
        successCount++;
      }
      if (result.allGatesPassed) {
        gatesPassedCount++;
      }

      const totalTime = (Date.now() - startTime) / 1000;
      await this.generateFinalReport(totalTime, successCount, gatesPassedCount);

    } catch (error) {
      console.error(`❌ 8192×8192 matrix multiplication failed:`, error);
      
      const testResult: TestResult = {
        iteration: 1,
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
        totalBlocks: 0,
        matrixSize: this.config.size,
        blockSize: this.config.block
      };
      
      this.results.push(testResult);
      
      const totalTime = (Date.now() - startTime) / 1000;
      await this.generateFinalReport(totalTime, successCount, gatesPassedCount);
    }
  }

  private async generateFinalReport(totalTime: number, successCount: number, gatesPassedCount: number): Promise<void> {
    console.log('\n🎯 FINAL TEST RESULTS');
    console.log('='.repeat(70));
    
    // Overall statistics
    console.log(`Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`Block size: ${this.config.block}×${this.config.block}`);
    console.log(`Test result: ${successCount > 0 ? '✅ SUCCESS' : '❌ FAILED'}`);
    console.log(`Gates passed: ${gatesPassedCount > 0 ? '✅ YES' : '❌ NO'}`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);

    // Performance statistics
    const successfulResults = this.results.filter(r => r.success);
    if (successfulResults.length > 0) {
      const result = successfulResults[0];
      console.log('\n📊 Performance Results:');
      console.log(`  Throughput: ${result.throughput.toFixed(2)} Gbit/s`);
      console.log(`  Transport p99: ${result.transportP99.toFixed(2)} ms`);
      console.log(`  Storage p99: ${result.storageP99.toFixed(2)} ms`);
      console.log(`  Compute p99: ${result.computeP99.toFixed(2)} ms`);
      console.log(`  E2E p99: ${result.e2eP99.toFixed(2)} ms`);
      console.log(`  Window closure: ${result.windowClosure.toFixed(2)}%`);
      console.log(`  Reject rate: ${result.rejectRate.toFixed(2)}%`);
      console.log(`  Total blocks processed: ${result.totalBlocks}`);
      console.log(`  Duration: ${(result.duration / 1000).toFixed(2)} seconds`);
    }

    // Gate analysis
    console.log('\n🚪 Gate Analysis:');
    const gateResults = this.results.filter(r => r.success).map(r => r.allGatesPassed);
    const gatesPassedRate = gateResults.length > 0 ? (gateResults.filter(Boolean).length / gateResults.length * 100) : 0;
    console.log(`  Gates passed rate: ${gatesPassedRate.toFixed(1)}%`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/8192-matrices-test-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        matrixSize: this.config.size,
        blockSize: this.config.block,
        totalIterations: 1,
        successfulIterations: successCount,
        gatesPassedIterations: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerIteration: totalTime
      },
      performance: successfulResults.length > 0 ? {
        throughput: successfulResults[0].throughput,
        transportP99: successfulResults[0].transportP99,
        storageP99: successfulResults[0].storageP99,
        computeP99: successfulResults[0].computeP99,
        e2eP99: successfulResults[0].e2eP99,
        windowClosure: successfulResults[0].windowClosure,
        rejectRate: successfulResults[0].rejectRate,
        totalBlocks: successfulResults[0].totalBlocks,
        duration: successfulResults[0].duration
      } : null,
      detailedResults: this.results
    };

    fs.writeFileSync(resultsFile, JSON.stringify(reportData, null, 2));
    console.log(`\n💾 Detailed results saved to: ${resultsFile}`);

    // Final verdict
    console.log('\n🏁 TEST VERDICT:');
    if (successCount > 0 && gatesPassedCount > 0) {
      console.log('✅ EXCELLENT: 8192×8192 matrix multiplication completed successfully with all gates passed');
    } else if (successCount > 0) {
      console.log('⚠️  PARTIAL: Matrix multiplication completed but some gates failed');
    } else {
      console.log('❌ FAILED: 8192×8192 matrix multiplication failed');
    }

    // Performance comparison
    if (successfulResults.length > 0) {
      const result = successfulResults[0];
      console.log('\n📈 Performance Analysis:');
      console.log(`  Matrix size: ${result.matrixSize}×${result.matrixSize} = ${(result.matrixSize * result.matrixSize).toLocaleString()} elements`);
      console.log(`  Block size: ${result.blockSize}×${result.blockSize} = ${(result.blockSize * result.blockSize).toLocaleString()} elements per block`);
      console.log(`  Total blocks: ${result.totalBlocks.toLocaleString()}`);
      console.log(`  Processing rate: ${(result.totalBlocks / (result.duration / 1000)).toFixed(1)} blocks/second`);
      console.log(`  Data throughput: ${result.throughput.toFixed(2)} Gbit/s`);
      
      if (result.throughput >= this.config.targetGbps) {
        console.log(`  ✅ Throughput target met: ${result.throughput.toFixed(2)} ≥ ${this.config.targetGbps} Gbit/s`);
      } else {
        console.log(`  ❌ Throughput target missed: ${result.throughput.toFixed(2)} < ${this.config.targetGbps} Gbit/s`);
      }
    }
  }
}

// Main execution
async function main() {
  const test = new Matrix8192Test();
  
  try {
    await test.run8192Matrices();
    console.log('\n🎉 8192×8192 matrix multiplication test completed!');
  } catch (error) {
    console.error('❌ Test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

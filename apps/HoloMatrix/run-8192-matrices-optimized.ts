/**
 * Run Optimized 8192×8192 Matrix Multiplication Test
 * Enhanced with high-performance optimizations and parallel processing
 */

import { OptimizedMatMulStep } from './src/steps/05-matmul-optimized';
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
  optimizationFeatures: string[];
}

class OptimizedMatrix8192Test {
  private config: MatMulConfig;
  private results: TestResult[] = [];
  private optimizationFeatures: string[] = [];

  constructor() {
    // Configure for 8192×8192 matrices with maximum optimization
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 8192,       // 8192×8192 matrix
      block: 256,       // Larger blocks for efficiency (256×256)
      lanes: 1024,      // Maximum lanes for highest throughput (increased from 512)
      payload: 32768,   // Maximum payload size (increased from 16384)
      batch: 128,       // Maximum batch size (increased from 64)
      workers: 64,      // Maximum workers for parallel processing (increased from 32)
      window: 50,       // Minimal window for lowest latency (reduced from 100)
      targetGbps: 100.0 // Ultra-high target for large matrices (increased from 50.0)
    };
  }

  async runOptimized8192Matrices(): Promise<void> {
    console.log('🚀 HOLOMATRIX OPTIMIZED 8192×8192 MATRIX MULTIPLICATION TEST');
    console.log('='.repeat(80));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Lanes: ${this.config.lanes}`);
    console.log(`  Workers: ${this.config.workers}`);
    console.log(`  Payload: ${this.config.payload}B`);
    console.log(`  Batch: ${this.config.batch}`);
    console.log(`  Window: ${this.config.window}ms`);
    console.log('='.repeat(80));

    const startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;

    // Calculate expected blocks and memory requirements
    const blockCount = Math.ceil(this.config.size / this.config.block);
    const totalBlocks = blockCount * blockCount * 2; // A and B matrices
    const blockDataSize = this.config.block * this.config.block * 2; // 2 bytes per Int16
    const totalDataSize = totalBlocks * blockDataSize;
    
    console.log(`\n📊 Expected blocks: ${totalBlocks} (${blockCount}×${blockCount} per matrix)`);
    console.log(`📊 Block data size: ${blockDataSize.toLocaleString()} bytes per block`);
    console.log(`📊 Total data size: ~${(totalDataSize / 1024 / 1024).toFixed(1)} MB`);
    console.log(`📊 Memory per matrix: ~${(this.config.size * this.config.size * 2 / 1024 / 1024).toFixed(1)} MB`);

    // Optimization features
    this.optimizationFeatures = [
      'Async matrix initialization with progress tracking',
      'High-performance worker pool with 64+ threads',
      'Parallel matrix processing across 1024 lanes',
      'Optimized block matrix multiplication with vectorization',
      'Zero-copy operations where possible',
      'Advanced compression algorithms',
      'Real-time performance monitoring',
      'Hardware-accelerated computations'
    ];

    console.log(`\n🔧 Optimization Features:`);
    this.optimizationFeatures.forEach((feature, index) => {
      console.log(`  ${index + 1}. ${feature}`);
    });

    try {
      console.log(`\n📊 Running optimized 8192×8192 matrix multiplication...`);
      
      const iterationStart = Date.now();
      const matMul = new OptimizedMatMulStep(this.config);
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
        blockSize: this.config.block,
        optimizationFeatures: this.optimizationFeatures
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
      console.error(`❌ Optimized 8192×8192 matrix multiplication failed:`, error);
      
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
        blockSize: this.config.block,
        optimizationFeatures: this.optimizationFeatures
      };
      
      this.results.push(testResult);
      
      const totalTime = (Date.now() - startTime) / 1000;
      await this.generateFinalReport(totalTime, successCount, gatesPassedCount);
    }
  }

  private async generateFinalReport(totalTime: number, successCount: number, gatesPassedCount: number): Promise<void> {
    console.log('\n🎯 FINAL OPTIMIZED TEST RESULTS');
    console.log('='.repeat(80));
    
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
      console.log(`  Total blocks processed: ${result.totalBlocks.toLocaleString()}`);
      console.log(`  Duration: ${(result.duration / 1000).toFixed(2)} seconds`);
    }

    // Optimization analysis
    console.log('\n🔧 Optimization Analysis:');
    const result = successfulResults[0];
    if (result) {
      const matrixElements = result.matrixSize * result.matrixSize;
      const blockElements = result.blockSize * result.blockSize;
      const processingRate = result.totalBlocks / (result.duration / 1000);
      const dataThroughput = result.throughput;
      
      console.log(`  Matrix elements: ${matrixElements.toLocaleString()}`);
      console.log(`  Block elements: ${blockElements.toLocaleString()}`);
      console.log(`  Processing rate: ${processingRate.toFixed(1)} blocks/second`);
      console.log(`  Data throughput: ${dataThroughput.toFixed(2)} Gbit/s`);
      
      // Performance comparison with theoretical maximum
      const theoreticalMax = (this.config.lanes * this.config.payload * 8) / 1e9; // Theoretical max in Gbit/s
      const efficiency = (dataThroughput / theoreticalMax) * 100;
      console.log(`  Theoretical max: ${theoreticalMax.toFixed(2)} Gbit/s`);
      console.log(`  Efficiency: ${efficiency.toFixed(1)}%`);
      
      if (dataThroughput >= this.config.targetGbps) {
        console.log(`  ✅ Throughput target met: ${dataThroughput.toFixed(2)} ≥ ${this.config.targetGbps} Gbit/s`);
      } else {
        console.log(`  ❌ Throughput target missed: ${dataThroughput.toFixed(2)} < ${this.config.targetGbps} Gbit/s`);
      }
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
    const resultsFile = `${resultsDir}/8192-matrices-optimized-test-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      optimizationFeatures: this.optimizationFeatures,
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
      console.log('✅ EXCELLENT: Optimized 8192×8192 matrix multiplication completed successfully with all gates passed');
      console.log('🚀 The Hologram system can now handle large matrix operations with high performance!');
    } else if (successCount > 0) {
      console.log('⚠️  PARTIAL: Matrix multiplication completed but some gates failed');
      console.log('🔧 Consider further optimizations for gate requirements');
    } else {
      console.log('❌ FAILED: Optimized 8192×8192 matrix multiplication failed');
      console.log('🔧 System may need additional resources or configuration adjustments');
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
      
      // Memory efficiency
      const memoryPerMatrix = result.matrixSize * result.matrixSize * 2; // 2 bytes per Int16
      const memoryEfficiency = (result.throughput * 1e9 / 8) / (memoryPerMatrix / (result.duration / 1000));
      console.log(`  Memory efficiency: ${memoryEfficiency.toFixed(2)} bytes/second per byte of data`);
      
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
  const test = new OptimizedMatrix8192Test();
  
  try {
    await test.runOptimized8192Matrices();
    console.log('\n🎉 Optimized 8192×8192 matrix multiplication test completed!');
  } catch (error) {
    console.error('❌ Test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

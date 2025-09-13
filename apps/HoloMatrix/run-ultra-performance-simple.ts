/**
 * Ultra Performance Test: 128 lanes, 500 iterations, batch 512 (Simplified)
 * Maximum performance optimization for ultra-high throughput testing
 * Targets 2048×2048 matrix size with ≥25 Gbit/s throughput
 * Optimized for 128 lanes, 500 iterations, and batch size 512
 */

import { MatMulStep } from './src/steps/05-matmul';
import { createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';

interface UltraPerformanceResult {
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
  matrixSize: string;
  lanesUsed: number;
  batchSize: number;
}

class UltraPerformanceMatrixTest {
  private config: MatMulConfig;
  private results: UltraPerformanceResult[] = [];
  private startTime: number = 0;

  constructor() {
    // Ultra-optimized configuration for maximum performance
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 2048,       // 2048×2048 matrix
      block: 128,       // 128×128 blocks
      lanes: 128,       // 128 lanes for ultra performance
      payload: 16384,   // Maximum payload for efficiency
      batch: 512,       // Ultra-large batch size (512)
      workers: 32,      // Maximum workers for parallel processing
      window: 25,       // Minimal window for lowest latency
      targetGbps: 25.0  // Target throughput
    };
  }

  async runUltraPerformanceTest(): Promise<void> {
    console.log('🚀 HOLOMATRIX ULTRA PERFORMANCE TEST (SIMPLIFIED)');
    console.log('='.repeat(80));
    console.log(`Ultra Performance Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Lanes: ${this.config.lanes} (ULTRA PERFORMANCE)`);
    console.log(`  Payload: ${this.config.payload}B (maximum for efficiency)`);
    console.log(`  Batch: ${this.config.batch} (ULTRA-LARGE BATCH)`);
    console.log(`  Workers: ${this.config.workers} (maximum parallel processing)`);
    console.log(`  Window: ${this.config.window}ms (minimal for lowest latency)`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Iterations: 500 (ULTRA PERFORMANCE MODE)`);
    console.log('='.repeat(80));

    this.startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;
    let totalThroughput = 0;

    // Run 500 matrix operations in ultra performance mode
    for (let i = 1; i <= 500; i++) {
      try {
        const iterationStart = Date.now();
        
        // Create ultra-optimized matmul instance for this iteration
        const matMul = new MatMulStep(this.config);
        
        // Run the pipeline with ultra performance optimizations
        const result = await this.runUltraPerformanceMatMul(matMul, i);
        const duration = Date.now() - iterationStart;

        const ultraPerformanceResult: UltraPerformanceResult = {
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
          totalBlocks: result.matrixStats.totalBlocks,
          matrixSize: `${this.config.size}×${this.config.size}`,
          lanesUsed: this.config.lanes,
          batchSize: this.config.batch
        };

        this.results.push(ultraPerformanceResult);

        if (result.success) {
          successCount++;
          totalThroughput += result.metrics.throughputGbps;
        }
        if (result.allGatesPassed) {
          gatesPassedCount++;
        }

        // Progress reporting every 25 iterations
        if (i % 25 === 0) {
          this.reportProgress(i, successCount, gatesPassedCount, totalThroughput);
        }

        // Ultra-performance optimization: minimal delay between operations
        if (i < 500) {
          await this.ultraOptimizedDelay(duration, result.metrics.throughputGbps);
        }

      } catch (error) {
        console.error(`❌ Iteration ${i} failed:`, error);
        
        const ultraPerformanceResult: UltraPerformanceResult = {
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
          totalBlocks: 0,
          matrixSize: `${this.config.size}×${this.config.size}`,
          lanesUsed: this.config.lanes,
          batchSize: this.config.batch
        };
        
        this.results.push(ultraPerformanceResult);
      }
    }

    const totalTime = (Date.now() - this.startTime) / 1000;
    await this.generateReport(totalTime, successCount, gatesPassedCount, totalThroughput);
  }

  private async runUltraPerformanceMatMul(matMul: MatMulStep, iteration: number): Promise<any> {
    // Ultra-optimize for performance by completely suppressing console output
    const originalLog = console.log;
    const originalError = console.error;
    
    if (iteration > 1) {
      console.log = () => {};
      console.error = () => {};
    }

    try {
      const result = await matMul.runMatMulPipeline();
      return result;
    } finally {
      console.log = originalLog;
      console.error = originalError;
    }
  }

  private async ultraOptimizedDelay(duration: number, throughput: number): Promise<void> {
    // Ultra-dynamic delay based on performance
    if (throughput >= 35.0) {
      // Excellent performance - no delay
      return;
    } else if (throughput >= 30.0) {
      // Very good performance - minimal delay
      await new Promise(resolve => setTimeout(resolve, 1));
    } else if (throughput >= 25.0) {
      // Good performance - small delay
      await new Promise(resolve => setTimeout(resolve, 2));
    } else if (throughput >= 20.0) {
      // Acceptable performance - moderate delay
      await new Promise(resolve => setTimeout(resolve, 5));
    } else {
      // Lower performance - longer delay
      await new Promise(resolve => setTimeout(resolve, 10));
    }
  }

  private reportProgress(iteration: number, successCount: number, gatesPassedCount: number, totalThroughput: number): void {
    const elapsed = (Date.now() - this.startTime) / 1000;
    const avgTimePerIteration = elapsed / iteration;
    const estimatedRemaining = (500 - iteration) * avgTimePerIteration;
    const avgThroughput = successCount > 0 ? totalThroughput / successCount : 0;
    
    console.log(`\n📈 Ultra Performance Progress (${iteration}/500):`);
    console.log(`  Success rate: ${(successCount / iteration * 100).toFixed(1)}%`);
    console.log(`  Gates passed: ${(gatesPassedCount / iteration * 100).toFixed(1)}%`);
    console.log(`  Avg throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Avg time per iteration: ${avgTimePerIteration.toFixed(2)}s`);
    console.log(`  Estimated remaining: ${(estimatedRemaining / 60).toFixed(1)} minutes`);
    console.log(`  Lanes: ${this.config.lanes} | Batch: ${this.config.batch}`);
  }

  private async generateReport(totalTime: number, successCount: number, gatesPassedCount: number, totalThroughput: number): Promise<void> {
    console.log('\n🎯 ULTRA PERFORMANCE TEST RESULTS');
    console.log('='.repeat(80));
    
    // Overall statistics
    console.log(`Total operations: 500`);
    console.log(`Successful operations: ${successCount} (${(successCount / 500 * 100).toFixed(1)}%)`);
    console.log(`Gates passed operations: ${gatesPassedCount} (${(gatesPassedCount / 500 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per operation: ${(totalTime / 500).toFixed(2)} seconds`);

    // Ultra performance statistics
    const successfulResults = this.results.filter(r => r.success);
    if (successfulResults.length > 0) {
      const avgThroughput = totalThroughput / successfulResults.length;
      const avgTransportP99 = successfulResults.reduce((sum, r) => sum + r.transportP99, 0) / successfulResults.length;
      const avgStorageP99 = successfulResults.reduce((sum, r) => sum + r.storageP99, 0) / successfulResults.length;
      const avgComputeP99 = successfulResults.reduce((sum, r) => sum + r.computeP99, 0) / successfulResults.length;
      const avgE2eP99 = successfulResults.reduce((sum, r) => sum + r.e2eP99, 0) / successfulResults.length;
      const avgWindowClosure = successfulResults.reduce((sum, r) => sum + r.windowClosure, 0) / successfulResults.length;
      const avgRejectRate = successfulResults.reduce((sum, r) => sum + r.rejectRate, 0) / successfulResults.length;

      console.log('\n📊 Ultra Performance Averages:');
      console.log(`  Average Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Transport p99: ${avgTransportP99.toFixed(2)} ms`);
      console.log(`  Storage p99: ${avgStorageP99.toFixed(2)} ms`);
      console.log(`  Compute p99: ${avgComputeP99.toFixed(2)} ms`);
      console.log(`  E2E p99: ${avgE2eP99.toFixed(2)} ms`);
      console.log(`  Window closure: ${avgWindowClosure.toFixed(2)}%`);
      console.log(`  Reject rate: ${avgRejectRate.toFixed(2)}%`);
    }

    // Ultra performance efficiency metrics
    const performanceEfficiency = (successCount / 500) * 100;
    const throughputEfficiency = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    const peakEfficiency = successfulResults.length > 0 ?
      (successfulResults.filter(r => r.throughput >= 30.0).length / successfulResults.length) * 100 : 0;
    
    console.log('\n🚀 Ultra Performance Efficiency:');
    console.log(`  Operation success rate: ${performanceEfficiency.toFixed(1)}%`);
    console.log(`  Throughput target achievement: ${throughputEfficiency.toFixed(1)}%`);
    console.log(`  Peak throughput achievement: ${peakEfficiency.toFixed(1)}%`);
    console.log(`  Lanes utilized: ${this.config.lanes}`);
    console.log(`  Batch size: ${this.config.batch}`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/ultra-performance-simple-128lanes-500iter-batch512-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        totalOperations: 500,
        successfulOperations: successCount,
        gatesPassedOperations: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerOperation: totalTime / 500,
        performanceEfficiency,
        throughputEfficiency,
        peakEfficiency
      },
      performance: successfulResults.length > 0 ? {
        averageThroughput: totalThroughput / successfulResults.length,
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

    // Final ultra performance verdict
    console.log('\n🏁 ULTRA PERFORMANCE TEST VERDICT:');
    if (successCount >= 490 && gatesPassedCount >= 480 && throughputEfficiency >= 90) {
      console.log('✅ OUTSTANDING: Ultra performance test exceeded all expectations');
    } else if (successCount >= 475 && gatesPassedCount >= 450 && throughputEfficiency >= 85) {
      console.log('✅ EXCELLENT: Ultra performance test passed with outstanding performance');
    } else if (successCount >= 450 && gatesPassedCount >= 400 && throughputEfficiency >= 75) {
      console.log('✅ VERY GOOD: Ultra performance test passed with excellent performance');
    } else if (successCount >= 400 && gatesPassedCount >= 350 && throughputEfficiency >= 60) {
      console.log('✅ GOOD: Ultra performance test passed with good performance');
    } else if (successCount >= 350) {
      console.log('⚠️  MARGINAL: Ultra performance test completed but with concerning performance');
    } else {
      console.log('❌ POOR: Ultra performance test failed with high failure rates');
    }

    // Ultra performance summary
    const throughputAchievement = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    
    console.log(`\n🎯 Ultra Performance Summary:`);
    console.log(`  Lanes utilized: ${this.config.lanes} (as requested)`);
    console.log(`  Batch size: ${this.config.batch} (as requested)`);
    console.log(`  Iterations completed: 500 (as requested)`);
    console.log(`  Throughput achievement: ${throughputAchievement.toFixed(1)}% of operations met ≥25 Gbit/s target`);
    console.log(`  Matrix size: 2048×2048 with 128×128 blocks`);
    console.log(`  Ultra performance mode: ENABLED`);
  }
}

// Main execution
async function main() {
  const test = new UltraPerformanceMatrixTest();
  
  try {
    await test.runUltraPerformanceTest();
    console.log('\n🎉 Ultra performance test completed!');
  } catch (error) {
    console.error('❌ Ultra performance test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

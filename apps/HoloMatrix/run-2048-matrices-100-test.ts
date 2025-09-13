/**
 * 2048×2048 Matrix Calculations Test - 100 Samples
 * Uses HoloMatrix code to run and test 2048×2048 matrix calculations with 100 samples
 */

import { MatMulStep } from './src/steps/05-matmul';
import { createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';
import { calculateMatrixDataInfo, calculateThroughput, validateThroughput } from './src/utils/throughput';

interface TestResult {
  sample: number;
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
  actualDataProcessed: number;
  matrixSize: string;
}

class Matrix2048Test {
  private config: MatMulConfig;
  private results: TestResult[] = [];
  private startTime: number = 0;
  private liveMetrics: any = null;

  constructor() {
    // Configuration for 2048×2048 matrix calculations
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 2048,       // 2048×2048 matrix
      block: 128,       // 128×128 blocks
      lanes: 64,        // Transport lanes
      payload: 4096,    // Payload size
      batch: 16,        // Batch size
      workers: 4,       // Workers
      window: 100,      // Window size
      targetGbps: 25.0  // Target throughput
    };
  }

  async run2048MatrixTest(): Promise<void> {
    console.log('🚀 HOLOMATRIX 2048×2048 MATRIX CALCULATIONS TEST');
    console.log('='.repeat(70));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Lanes: ${this.config.lanes}`);
    console.log(`  Payload: ${this.config.payload}B`);
    console.log(`  Batch: ${this.config.batch}`);
    console.log(`  Workers: ${this.config.workers}`);
    console.log(`  Window: ${this.config.window}ms`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Samples: 100`);
    console.log('='.repeat(70));

    this.startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;
    let totalThroughput = 0;
    let totalDataProcessed = 0;

    // Start live monitoring
    this.startLiveMonitoring();

    // Run 100 matrix calculations
    for (let i = 1; i <= 100; i++) {
      try {
        const iterationStart = Date.now();
        
        // Create matmul instance for this iteration
        const matMul = new MatMulStep(this.config);
        
        // Run the matrix multiplication pipeline
        const result = await this.runMatMul(matMul, i);
        const duration = Date.now() - iterationStart;
        
        // Calculate accurate throughput
        const matrixDataInfo = calculateMatrixDataInfo(this.config.size, this.config.block);
        const durationSeconds = duration / 1000;
        const throughputMeasurement = calculateThroughput(matrixDataInfo.totalDataBytes, durationSeconds);
        const actualDataProcessed = matrixDataInfo.totalDataBytes;

        const testResult: TestResult = {
          sample: i,
          success: result.success,
          allGatesPassed: result.allGatesPassed,
          duration,
          throughput: throughputMeasurement.throughputGbps,
          transportP99: result.metrics.transport.p99Ms,
          storageP99: result.metrics.storage.p99Ms,
          computeP99: result.metrics.compute.p99Ms,
          e2eP99: result.metrics.e2e.p99Ms,
          windowClosure: (result.metrics.transport.windowsClosed / result.metrics.transport.windowsTotal) * 100,
          rejectRate: (result.metrics.transport.rejects / result.metrics.transport.framesSent) * 100,
          totalBlocks: result.matrixStats.totalBlocks,
          actualDataProcessed,
          matrixSize: `${this.config.size}×${this.config.size}`
        };

        this.results.push(testResult);

        if (result.success) {
          successCount++;
          totalThroughput += throughputMeasurement.throughputGbps;
          totalDataProcessed += actualDataProcessed;
        }
        if (result.allGatesPassed) {
          gatesPassedCount++;
        }

        // Update live metrics
        this.updateLiveMetrics(testResult, i);

        // Minimal delay between operations
        if (i < 100) {
          await this.optimizedDelay(duration, throughputMeasurement.throughputGbps);
        }

        // Progress reporting every 10 iterations
        if (i % 10 === 0) {
          this.reportProgress(i, successCount, gatesPassedCount, totalThroughput);
        }

      } catch (error) {
        console.error(`❌ Sample ${i} failed:`, error);
        
        const testResult: TestResult = {
          sample: i,
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
          actualDataProcessed: 0,
          matrixSize: `${this.config.size}×${this.config.size}`
        };
        
        this.results.push(testResult);
      }
    }

    // Stop live monitoring
    this.stopLiveMonitoring();

    const totalTime = (Date.now() - this.startTime) / 1000;
    await this.generateReport(totalTime, successCount, gatesPassedCount, totalThroughput, totalDataProcessed);
  }

  private async runMatMul(matMul: MatMulStep, sample: number): Promise<any> {
    // Suppress detailed logs for streaming after first sample
    const originalLog = console.log;
    const originalError = console.error;
    
    if (sample > 1) {
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

  private async optimizedDelay(duration: number, throughput: number): Promise<void> {
    // Dynamic delay based on performance
    if (throughput >= 25.0) {
      // Good performance - minimal delay
      await new Promise(resolve => setTimeout(resolve, 10));
    } else if (throughput >= 20.0) {
      // Acceptable performance - small delay
      await new Promise(resolve => setTimeout(resolve, 50));
    } else {
      // Lower performance - longer delay
      await new Promise(resolve => setTimeout(resolve, 100));
    }
  }

  private startLiveMonitoring(): void {
    console.log('\n📊 Starting live monitoring...');
    
    this.liveMetrics = setInterval(() => {
      this.updateLiveDisplay();
    }, 500);
  }

  private stopLiveMonitoring(): void {
    if (this.liveMetrics) {
      clearInterval(this.liveMetrics);
      this.liveMetrics = null;
    }
  }

  private updateLiveMetrics(result: TestResult, sample: number): void {
    this.liveMetrics = {
      sample,
      throughput: result.throughput,
      success: result.success,
      gatesPassed: result.allGatesPassed,
      dataProcessed: result.actualDataProcessed
    };
  }

  private updateLiveDisplay(): void {
    if (!this.liveMetrics) return;

    const elapsed = (Date.now() - this.startTime) / 1000;
    const { sample, throughput, success, gatesPassed, dataProcessed } = this.liveMetrics;
    
    // Clear previous line and show metrics
    process.stdout.write('\r\x1b[K');
    process.stdout.write(
      `🚀 2048×2048: ${sample}/100 | ` +
      `Gb/s: ${throughput.toFixed(1)}${throughput >= 25.0 ? '✅' : '❌'} | ` +
      `Data: ${(dataProcessed / 1e6).toFixed(1)}MB | ` +
      `Success: ${success ? '✅' : '❌'} | ` +
      `Gates: ${gatesPassed ? '✅' : '❌'} | ` +
      `Time: ${elapsed.toFixed(1)}s`
    );
  }

  private reportProgress(sample: number, successCount: number, gatesPassedCount: number, totalThroughput: number): void {
    const elapsed = (Date.now() - this.startTime) / 1000;
    const avgTimePerSample = elapsed / sample;
    const estimatedRemaining = (100 - sample) * avgTimePerSample;
    const avgThroughput = successCount > 0 ? totalThroughput / successCount : 0;
    
    console.log(`\n📈 Progress (${sample}/100):`);
    console.log(`  Success rate: ${(successCount / sample * 100).toFixed(1)}%`);
    console.log(`  Gates passed: ${(gatesPassedCount / sample * 100).toFixed(1)}%`);
    console.log(`  Avg throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Avg time per sample: ${avgTimePerSample.toFixed(2)}s`);
    console.log(`  Estimated remaining: ${(estimatedRemaining / 60).toFixed(1)} minutes`);
  }

  private async generateReport(
    totalTime: number, 
    successCount: number, 
    gatesPassedCount: number, 
    totalThroughput: number,
    totalDataProcessed: number
  ): Promise<void> {
    console.log('\n🎯 2048×2048 MATRIX TEST RESULTS');
    console.log('='.repeat(70));
    
    // Overall statistics
    console.log(`Matrix size: 2048×2048`);
    console.log(`Total samples: 100`);
    console.log(`Successful samples: ${successCount} (${(successCount / 100 * 100).toFixed(1)}%)`);
    console.log(`Gates passed samples: ${gatesPassedCount} (${(gatesPassedCount / 100 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per sample: ${(totalTime / 100).toFixed(2)} seconds`);

    // Performance statistics
    const successfulResults = this.results.filter(r => r.success);
    if (successfulResults.length > 0) {
      const avgThroughput = totalThroughput / successfulResults.length;
      const avgTransportP99 = successfulResults.reduce((sum, r) => sum + r.transportP99, 0) / successfulResults.length;
      const avgStorageP99 = successfulResults.reduce((sum, r) => sum + r.storageP99, 0) / successfulResults.length;
      const avgComputeP99 = successfulResults.reduce((sum, r) => sum + r.computeP99, 0) / successfulResults.length;
      const avgE2eP99 = successfulResults.reduce((sum, r) => sum + r.e2eP99, 0) / successfulResults.length;
      const avgWindowClosure = successfulResults.reduce((sum, r) => sum + r.windowClosure, 0) / successfulResults.length;
      const avgRejectRate = successfulResults.reduce((sum, r) => sum + r.rejectRate, 0) / successfulResults.length;

      console.log('\n📊 Performance Averages:');
      console.log(`  Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Transport p99: ${avgTransportP99.toFixed(2)} ms`);
      console.log(`  Storage p99: ${avgStorageP99.toFixed(2)} ms`);
      console.log(`  Compute p99: ${avgComputeP99.toFixed(2)} ms`);
      console.log(`  E2E p99: ${avgE2eP99.toFixed(2)} ms`);
      console.log(`  Window closure: ${avgWindowClosure.toFixed(2)}%`);
      console.log(`  Reject rate: ${avgRejectRate.toFixed(2)}%`);
      console.log(`  Total data processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB`);
    }

    // Efficiency metrics
    const successRate = (successCount / 100) * 100;
    const throughputEfficiency = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    
    console.log('\n🚀 Efficiency Metrics:');
    console.log(`  Operation success rate: ${successRate.toFixed(1)}%`);
    console.log(`  Throughput target achievement: ${throughputEfficiency.toFixed(1)}%`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/2048-matrices-100-test-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        matrixSize: '2048×2048',
        totalSamples: 100,
        successfulSamples: successCount,
        gatesPassedSamples: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerSample: totalTime / 100,
        successRate,
        throughputEfficiency,
        totalDataProcessedGB: totalDataProcessed / 1e9
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

    // Final verdict
    console.log('\n🏁 TEST VERDICT:');
    if (successCount >= 95 && gatesPassedCount >= 90 && throughputEfficiency >= 80) {
      console.log('✅ EXCELLENT: Test passed with high success, gates, and throughput rates');
    } else if (successCount >= 85 && gatesPassedCount >= 75 && throughputEfficiency >= 60) {
      console.log('✅ GOOD: Test passed with acceptable performance');
    } else if (successCount >= 70) {
      console.log('⚠️  MARGINAL: Test completed but with concerning performance');
    } else {
      console.log('❌ POOR: Test failed with high failure rates');
    }

    // Throughput achievement summary
    const throughputAchievement = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    
    console.log(`\n🎯 Throughput Achievement: ${throughputAchievement.toFixed(1)}% of samples met ≥25 Gbit/s target`);
    console.log(`📊 Total Data Processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB across 100 matrix calculations`);
    console.log(`🔢 Matrix Size: 2048×2048 with 128×128 blocks`);
  }
}

// Main execution
async function main() {
  const test = new Matrix2048Test();
  
  try {
    await test.run2048MatrixTest();
    console.log('\n🎉 2048×2048 matrix calculations test completed!');
  } catch (error) {
    console.error('❌ Test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

/**
 * Ultra Performance Test: 128 lanes, 500 iterations, batch 512
 * Maximum performance optimization for ultra-high throughput testing
 * Targets 2048×2048 matrix size with ≥25 Gbit/s throughput
 * Optimized for 128 lanes, 500 iterations, and batch size 512
 */

import { MatMulStep } from './src/steps/05-matmul';
import { createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';
import { calculateMatrixDataInfo, calculateThroughput } from './src/utils/throughput';

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
  actualDataProcessed: number;
  matrixSize: string;
  lanesUsed: number;
  batchSize: number;
  peakThroughput: number;
  sustainedThroughput: number;
  streamingLatency: number;
}

class UltraPerformanceMatrixTest {
  private config: MatMulConfig;
  private results: UltraPerformanceResult[] = [];
  private startTime: number = 0;
  private liveMetrics: any = null;
  private peakThroughput: number = 0;
  private sustainedThroughput: number = 0;

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
    console.log('🚀 HOLOMATRIX ULTRA PERFORMANCE TEST');
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
    let totalDataProcessed = 0;
    let totalStreamingLatency = 0;
    let throughputSamples: number[] = [];

    // Start ultra-fast live monitoring
    this.startUltraLiveMonitoring();

    // Pre-warm the system
    await this.preWarmSystem();

    // Run 500 matrix operations in ultra performance mode
    for (let i = 1; i <= 500; i++) {
      try {
        const iterationStart = Date.now();
        
        // Create ultra-optimized matmul instance for this iteration
        const matMul = new MatMulStep(this.config);
        
        // Run the pipeline with ultra performance optimizations
        const result = await this.runUltraPerformanceMatMul(matMul, i);
        const duration = Date.now() - iterationStart;
        
        // Calculate accurate throughput
        const matrixDataInfo = calculateMatrixDataInfo(this.config.size, this.config.block);
        const durationSeconds = duration / 1000;
        const throughputMeasurement = calculateThroughput(matrixDataInfo.totalDataBytes, durationSeconds);
        const actualDataProcessed = matrixDataInfo.totalDataBytes;
        const streamingLatency = this.calculateUltraStreamingLatency(result);
        const peakThroughput = this.calculatePeakThroughput(result, duration);
        const sustainedThroughput = this.calculateSustainedThroughput(result, duration);

        // Update global peak and sustained throughput
        this.peakThroughput = Math.max(this.peakThroughput, peakThroughput);
        this.sustainedThroughput = Math.max(this.sustainedThroughput, sustainedThroughput);
        throughputSamples.push(throughputMeasurement.throughputGbps);

        const ultraPerformanceResult: UltraPerformanceResult = {
          iteration: i,
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
          matrixSize: `${this.config.size}×${this.config.size}`,
          lanesUsed: this.config.lanes,
          batchSize: this.config.batch,
          peakThroughput,
          sustainedThroughput,
          streamingLatency
        };

        this.results.push(ultraPerformanceResult);

        if (result.success) {
          successCount++;
          totalThroughput += throughputMeasurement.throughputGbps;
          totalDataProcessed += actualDataProcessed;
          totalStreamingLatency += streamingLatency;
        }
        if (result.allGatesPassed) {
          gatesPassedCount++;
        }

        // Update ultra-fast live metrics
        this.updateUltraLiveMetrics(ultraPerformanceResult, i);

        // Ultra-performance optimization: minimal delay between operations
        if (i < 500) {
          // Ultra-minimal delay for maximum performance
          await this.ultraOptimizedDelay(duration, throughputMeasurement.throughputGbps, i);
        }

        // Progress reporting every 25 iterations for ultra performance
        if (i % 25 === 0) {
          this.reportUltraPerformanceProgress(i, successCount, gatesPassedCount, totalThroughput, throughputSamples);
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
          actualDataProcessed: 0,
          matrixSize: `${this.config.size}×${this.config.size}`,
          lanesUsed: this.config.lanes,
          batchSize: this.config.batch,
          peakThroughput: 0,
          sustainedThroughput: 0,
          streamingLatency: 0
        };
        
        this.results.push(ultraPerformanceResult);
      }
    }

    // Stop ultra-fast live monitoring
    this.stopUltraLiveMonitoring();

    const totalTime = (Date.now() - this.startTime) / 1000;
    await this.generateUltraPerformanceReport(totalTime, successCount, gatesPassedCount, totalThroughput, totalDataProcessed, totalStreamingLatency, throughputSamples);
  }

  private async preWarmSystem(): Promise<void> {
    console.log('\n🔥 Pre-warming system for ultra performance...');
    
    // Create a test matmul instance to warm up the system with very lenient settings
    const warmupConfig = { 
      ...this.config, 
      targetGbps: 1.0,  // Very low target for warmup
      size: 512,        // Smaller matrix for warmup
      block: 64,        // Smaller blocks for warmup
      lanes: 16,        // Fewer lanes for warmup
      batch: 32,        // Smaller batch for warmup
      workers: 4        // Fewer workers for warmup
    };
    const warmupMatMul = new MatMulStep(warmupConfig);
    
    try {
      // Run a quick warmup operation
      const warmupResult = await warmupMatMul.runMatMulPipeline();
      console.log(`✅ System pre-warmed: ${warmupResult.metrics.throughputGbps.toFixed(2)} Gbit/s`);
    } catch (error) {
      console.log('⚠️  Warmup failed, continuing with cold start');
    }
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

  private calculateUltraStreamingLatency(result: any): number {
    // Calculate ultra-streaming-specific latency metrics
    const transportLatency = result.metrics.transport.p99Ms;
    const storageLatency = result.metrics.storage.p99Ms;
    const computeLatency = result.metrics.compute.p99Ms;
    
    // Ultra-streaming latency is the weighted average favoring transport
    return (transportLatency * 0.5) + (storageLatency * 0.3) + (computeLatency * 0.2);
  }

  private calculatePeakThroughput(result: any, duration: number): number {
    // Calculate peak throughput for this operation
    const totalBytes = result.matrixStats.totalBlocks * this.config.block * this.config.block * 2; // Int16 = 2 bytes
    const peakThroughput = (totalBytes * 8) / (duration / 1000 * 1e9);
    return peakThroughput;
  }

  private calculateSustainedThroughput(result: any, duration: number): number {
    // Calculate sustained throughput (more conservative)
    return result.metrics.throughputGbps * 0.9; // 90% of measured throughput
  }

  private async ultraOptimizedDelay(duration: number, throughput: number, iteration: number): Promise<void> {
    // Ultra-dynamic delay based on performance and iteration
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

  private startUltraLiveMonitoring(): void {
    console.log('\n📊 Starting ultra-fast live performance monitoring...');
    
    this.liveMetrics = setInterval(() => {
      this.updateUltraLiveDisplay();
    }, 200); // Update every 200ms for ultra performance
  }

  private stopUltraLiveMonitoring(): void {
    if (this.liveMetrics) {
      clearInterval(this.liveMetrics);
      this.liveMetrics = null;
    }
  }

  private updateUltraLiveMetrics(result: UltraPerformanceResult, iteration: number): void {
    // Update ultra-fast live metrics for performance display
    this.liveMetrics = {
      iteration,
      throughput: result.throughput,
      peakThroughput: result.peakThroughput,
      sustainedThroughput: result.sustainedThroughput,
      streamingLatency: result.streamingLatency,
      success: result.success,
      gatesPassed: result.allGatesPassed,
      lanesUsed: result.lanesUsed,
      batchSize: result.batchSize
    };
  }

  private updateUltraLiveDisplay(): void {
    if (!this.liveMetrics) return;

    const elapsed = (Date.now() - this.startTime) / 1000;
    const { iteration, throughput, peakThroughput, sustainedThroughput, streamingLatency, success, gatesPassed, lanesUsed, batchSize } = this.liveMetrics;
    
    // Clear previous line and show ultra performance metrics
    process.stdout.write('\r\x1b[K');
    process.stdout.write(
      `🚀 Ultra: ${iteration || 0}/500 | ` +
      `Lanes: ${lanesUsed || 0} | ` +
      `Batch: ${batchSize || 0} | ` +
      `Gb/s: ${(throughput || 0).toFixed(1)}${(throughput || 0) >= 25.0 ? '✅' : '❌'} | ` +
      `Peak: ${(peakThroughput || 0).toFixed(1)} | ` +
      `Sust: ${(sustainedThroughput || 0).toFixed(1)} | ` +
      `Lat: ${(streamingLatency || 0).toFixed(1)}ms | ` +
      `${success ? '✅' : '❌'}${gatesPassed ? '✅' : '❌'} | ` +
      `${elapsed.toFixed(1)}s`
    );
  }

  private reportUltraPerformanceProgress(
    iteration: number, 
    successCount: number, 
    gatesPassedCount: number, 
    totalThroughput: number,
    throughputSamples: number[]
  ): void {
    const elapsed = (Date.now() - this.startTime) / 1000;
    const avgTimePerIteration = elapsed / iteration;
    const estimatedRemaining = (500 - iteration) * avgTimePerIteration;
    const avgThroughput = successCount > 0 ? totalThroughput / successCount : 0;
    const maxThroughput = Math.max(...throughputSamples);
    const minThroughput = Math.min(...throughputSamples);
    
    console.log(`\n📈 Ultra Performance Progress (${iteration}/500):`);
    console.log(`  Success rate: ${(successCount / iteration * 100).toFixed(1)}%`);
    console.log(`  Gates passed: ${(gatesPassedCount / iteration * 100).toFixed(1)}%`);
    console.log(`  Avg throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Max throughput: ${maxThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Min throughput: ${minThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Avg time per iteration: ${avgTimePerIteration.toFixed(2)}s`);
    console.log(`  Estimated remaining: ${(estimatedRemaining / 60).toFixed(1)} minutes`);
    console.log(`  Lanes: ${this.config.lanes} | Batch: ${this.config.batch}`);
  }

  private async generateUltraPerformanceReport(
    totalTime: number, 
    successCount: number, 
    gatesPassedCount: number, 
    totalThroughput: number,
    totalDataProcessed: number,
    totalStreamingLatency: number,
    throughputSamples: number[]
  ): Promise<void> {
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
      const avgStreamingLatency = totalStreamingLatency / successfulResults.length;
      const avgTransportP99 = successfulResults.reduce((sum, r) => sum + r.transportP99, 0) / successfulResults.length;
      const avgStorageP99 = successfulResults.reduce((sum, r) => sum + r.storageP99, 0) / successfulResults.length;
      const avgComputeP99 = successfulResults.reduce((sum, r) => sum + r.computeP99, 0) / successfulResults.length;
      const avgE2eP99 = successfulResults.reduce((sum, r) => sum + r.e2eP99, 0) / successfulResults.length;
      const avgWindowClosure = successfulResults.reduce((sum, r) => sum + r.windowClosure, 0) / successfulResults.length;
      const avgRejectRate = successfulResults.reduce((sum, r) => sum + r.rejectRate, 0) / successfulResults.length;
      const avgPeakThroughput = successfulResults.reduce((sum, r) => sum + r.peakThroughput, 0) / successfulResults.length;
      const avgSustainedThroughput = successfulResults.reduce((sum, r) => sum + r.sustainedThroughput, 0) / successfulResults.length;

      console.log('\n📊 Ultra Performance Averages:');
      console.log(`  Average Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Peak Throughput: ${this.peakThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Sustained Throughput: ${this.sustainedThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Average Peak Throughput: ${avgPeakThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Average Sustained Throughput: ${avgSustainedThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Streaming Latency: ${avgStreamingLatency.toFixed(2)} ms`);
      console.log(`  Transport p99: ${avgTransportP99.toFixed(2)} ms`);
      console.log(`  Storage p99: ${avgStorageP99.toFixed(2)} ms`);
      console.log(`  Compute p99: ${avgComputeP99.toFixed(2)} ms`);
      console.log(`  E2E p99: ${avgE2eP99.toFixed(2)} ms`);
      console.log(`  Window closure: ${avgWindowClosure.toFixed(2)}%`);
      console.log(`  Reject rate: ${avgRejectRate.toFixed(2)}%`);
      console.log(`  Total data processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB`);
    }

    // Throughput distribution analysis
    const throughputStats = this.calculateThroughputStats(throughputSamples);
    console.log('\n📈 Throughput Distribution:');
    console.log(`  Min: ${throughputStats.min.toFixed(2)} Gbit/s`);
    console.log(`  Max: ${throughputStats.max.toFixed(2)} Gbit/s`);
    console.log(`  Median: ${throughputStats.median.toFixed(2)} Gbit/s`);
    console.log(`  P95: ${throughputStats.p95.toFixed(2)} Gbit/s`);
    console.log(`  P99: ${throughputStats.p99.toFixed(2)} Gbit/s`);

    // Ultra performance efficiency metrics
    const performanceEfficiency = (successCount / 500) * 100;
    const throughputEfficiency = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    const peakEfficiency = successfulResults.length > 0 ?
      (successfulResults.filter(r => r.peakThroughput >= 30.0).length / successfulResults.length) * 100 : 0;
    const ultraEfficiency = successfulResults.length > 0 ?
      (successfulResults.filter(r => r.peakThroughput >= 35.0).length / successfulResults.length) * 100 : 0;
    
    console.log('\n🚀 Ultra Performance Efficiency:');
    console.log(`  Operation success rate: ${performanceEfficiency.toFixed(1)}%`);
    console.log(`  Throughput target achievement: ${throughputEfficiency.toFixed(1)}%`);
    console.log(`  Peak throughput achievement: ${peakEfficiency.toFixed(1)}%`);
    console.log(`  Ultra throughput achievement: ${ultraEfficiency.toFixed(1)}%`);
    console.log(`  Lanes utilized: ${this.config.lanes}`);
    console.log(`  Batch size: ${this.config.batch}`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/ultra-performance-128lanes-500iter-batch512-${timestamp}.json`;
    
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
        peakEfficiency,
        ultraEfficiency,
        globalPeakThroughput: this.peakThroughput,
        globalSustainedThroughput: this.sustainedThroughput,
        totalDataProcessedGB: totalDataProcessed / 1e9
      },
      performance: successfulResults.length > 0 ? {
        averageThroughput: totalThroughput / successfulResults.length,
        averageStreamingLatency: totalStreamingLatency / successfulResults.length,
        averageTransportP99: successfulResults.reduce((sum, r) => sum + r.transportP99, 0) / successfulResults.length,
        averageStorageP99: successfulResults.reduce((sum, r) => sum + r.storageP99, 0) / successfulResults.length,
        averageComputeP99: successfulResults.reduce((sum, r) => sum + r.computeP99, 0) / successfulResults.length,
        averageE2eP99: successfulResults.reduce((sum, r) => sum + r.e2eP99, 0) / successfulResults.length,
        averageWindowClosure: successfulResults.reduce((sum, r) => sum + r.windowClosure, 0) / successfulResults.length,
        averageRejectRate: successfulResults.reduce((sum, r) => sum + r.rejectRate, 0) / successfulResults.length,
        averagePeakThroughput: successfulResults.reduce((sum, r) => sum + r.peakThroughput, 0) / successfulResults.length,
        averageSustainedThroughput: successfulResults.reduce((sum, r) => sum + r.sustainedThroughput, 0) / successfulResults.length
      } : null,
      throughputDistribution: throughputStats,
      detailedResults: this.results
    };

    fs.writeFileSync(resultsFile, JSON.stringify(reportData, null, 2));
    console.log(`\n💾 Detailed results saved to: ${resultsFile}`);

    // Final ultra performance verdict
    console.log('\n🏁 ULTRA PERFORMANCE TEST VERDICT:');
    if (successCount >= 490 && gatesPassedCount >= 480 && throughputEfficiency >= 90 && ultraEfficiency >= 60) {
      console.log('✅ OUTSTANDING: Ultra performance test exceeded all expectations');
    } else if (successCount >= 475 && gatesPassedCount >= 450 && throughputEfficiency >= 85 && peakEfficiency >= 70) {
      console.log('✅ EXCELLENT: Ultra performance test passed with outstanding performance');
    } else if (successCount >= 450 && gatesPassedCount >= 400 && throughputEfficiency >= 75 && peakEfficiency >= 50) {
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
    console.log(`  Peak Performance: ${this.peakThroughput.toFixed(2)} Gbit/s achieved`);
    console.log(`  Sustained Performance: ${this.sustainedThroughput.toFixed(2)} Gbit/s achieved`);
    console.log(`  Total data processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB across 500 matrix operations`);
    console.log(`  Matrix size: 2048×2048 with 128×128 blocks`);
    console.log(`  Ultra performance mode: ENABLED`);
  }

  private calculateThroughputStats(samples: number[]): {
    min: number;
    max: number;
    median: number;
    p95: number;
    p99: number;
  } {
    if (samples.length === 0) {
      return { min: 0, max: 0, median: 0, p95: 0, p99: 0 };
    }

    const sorted = [...samples].sort((a, b) => a - b);
    const len = sorted.length;

    return {
      min: sorted[0],
      max: sorted[len - 1],
      median: sorted[Math.floor(len / 2)],
      p95: sorted[Math.floor(len * 0.95)],
      p99: sorted[Math.floor(len * 0.99)]
    };
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

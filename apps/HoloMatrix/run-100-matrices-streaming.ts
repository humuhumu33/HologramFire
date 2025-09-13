/**
 * Streaming 100 Matrix Operations Test
 * Optimized for maximum throughput and streaming performance
 * Targets 2048×2048 matrix size with ≥25 Gbit/s throughput
 */

import { MatMulStep } from './src/steps/05-matmul';
import { createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';

interface StreamingResult {
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
  streamingLatency: number;
}

class StreamingMatrix100Test {
  private config: MatMulConfig;
  private results: StreamingResult[] = [];
  private startTime: number = 0;
  private liveMetrics: any = null;

  constructor() {
    // Optimized configuration for streaming 100 operations
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 2048,       // Required: 2048×2048 matrix
      block: 128,       // Required: 128×128 blocks
      lanes: 128,       // Increased lanes for higher throughput
      payload: 8192,    // Larger payload for better efficiency
      batch: 32,        // Larger batch size for streaming
      workers: 8,       // More workers for parallel processing
      window: 50,       // Smaller window for lower latency
      targetGbps: 25.0  // Required: 25 Gbit/s target
    };
  }

  async run100StreamingMatrices(): Promise<void> {
    console.log('🚀 HOLOMATRIX STREAMING 100 MATRIX OPERATIONS TEST');
    console.log('='.repeat(70));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Lanes: ${this.config.lanes} (increased for throughput)`);
    console.log(`  Payload: ${this.config.payload}B (larger for efficiency)`);
    console.log(`  Batch: ${this.config.batch} (larger for streaming)`);
    console.log(`  Workers: ${this.config.workers} (parallel processing)`);
    console.log(`  Window: ${this.config.window}ms (lower latency)`);
    console.log(`  Target: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Operations: 100 (streaming mode)`);
    console.log('='.repeat(70));

    this.startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;
    let totalThroughput = 0;
    let totalStreamingLatency = 0;

    // Start live monitoring
    this.startLiveMonitoring();

    // Run 100 matrix operations in streaming mode
    for (let i = 1; i <= 100; i++) {
      try {
        const iterationStart = Date.now();
        
        // Create optimized matmul instance for this iteration
        const matMul = new MatMulStep(this.config);
        
        // Run the pipeline with streaming optimizations
        const result = await this.runStreamingMatMul(matMul, i);
        const duration = Date.now() - iterationStart;
        const streamingLatency = this.calculateStreamingLatency(result);

        const streamingResult: StreamingResult = {
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
          streamingLatency
        };

        this.results.push(streamingResult);

        if (result.success) {
          successCount++;
          totalThroughput += result.metrics.throughputGbps;
          totalStreamingLatency += streamingLatency;
        }
        if (result.allGatesPassed) {
          gatesPassedCount++;
        }

        // Update live metrics
        this.updateLiveMetrics(streamingResult, i);

        // Streaming optimization: minimal delay between operations
        if (i < 100) {
          // Very small delay to maintain streaming but prevent overwhelming
          await this.optimizedDelay(duration, result.metrics.throughputGbps);
        }

        // Progress reporting every 10 iterations for streaming
        if (i % 10 === 0) {
          this.reportStreamingProgress(i, successCount, gatesPassedCount, totalThroughput);
        }

      } catch (error) {
        console.error(`❌ Iteration ${i} failed:`, error);
        
        const streamingResult: StreamingResult = {
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
          streamingLatency: 0
        };
        
        this.results.push(streamingResult);
      }
    }

    // Stop live monitoring
    this.stopLiveMonitoring();

    const totalTime = (Date.now() - this.startTime) / 1000;
    await this.generateStreamingReport(totalTime, successCount, gatesPassedCount, totalThroughput, totalStreamingLatency);
  }

  private async runStreamingMatMul(matMul: MatMulStep, iteration: number): Promise<any> {
    // Optimize for streaming by reducing console output
    const originalLog = console.log;
    if (iteration > 1) {
      console.log = () => {}; // Suppress detailed logs for streaming
    }

    try {
      const result = await matMul.runMatMulPipeline();
      return result;
    } finally {
      console.log = originalLog; // Restore logging
    }
  }

  private calculateStreamingLatency(result: any): number {
    // Calculate streaming-specific latency metrics
    const transportLatency = result.metrics.transport.p99Ms;
    const storageLatency = result.metrics.storage.p99Ms;
    const computeLatency = result.metrics.compute.p99Ms;
    
    // Streaming latency is the maximum of the three components
    return Math.max(transportLatency, storageLatency, computeLatency);
  }

  private async optimizedDelay(duration: number, throughput: number): Promise<void> {
    // Dynamic delay based on performance
    if (throughput >= 25.0) {
      // High performance - minimal delay
      await new Promise(resolve => setTimeout(resolve, 10));
    } else if (throughput >= 20.0) {
      // Good performance - small delay
      await new Promise(resolve => setTimeout(resolve, 50));
    } else {
      // Lower performance - longer delay to prevent overwhelming
      await new Promise(resolve => setTimeout(resolve, 100));
    }
  }

  private startLiveMonitoring(): void {
    console.log('\n📊 Starting live streaming monitoring...');
    
    this.liveMetrics = setInterval(() => {
      this.updateLiveDisplay();
    }, 500); // Update every 500ms for streaming
  }

  private stopLiveMonitoring(): void {
    if (this.liveMetrics) {
      clearInterval(this.liveMetrics);
      this.liveMetrics = null;
    }
  }

  private updateLiveMetrics(result: StreamingResult, iteration: number): void {
    // Update live metrics for streaming display
    this.liveMetrics = {
      iteration,
      throughput: result.throughput,
      streamingLatency: result.streamingLatency,
      success: result.success,
      gatesPassed: result.allGatesPassed
    };
  }

  private updateLiveDisplay(): void {
    if (!this.liveMetrics) return;

    const elapsed = (Date.now() - this.startTime) / 1000;
    const { iteration, throughput, streamingLatency, success, gatesPassed } = this.liveMetrics;
    
    // Clear previous line and show streaming metrics
    process.stdout.write('\r\x1b[K');
    process.stdout.write(
      `🚀 Streaming: ${iteration}/100 | ` +
      `Gb/s: ${throughput.toFixed(1)}${throughput >= 25.0 ? '✅' : '❌'} | ` +
      `Stream Lat: ${streamingLatency.toFixed(1)}ms | ` +
      `Success: ${success ? '✅' : '❌'} | ` +
      `Gates: ${gatesPassed ? '✅' : '❌'} | ` +
      `Time: ${elapsed.toFixed(1)}s`
    );
  }

  private reportStreamingProgress(iteration: number, successCount: number, gatesPassedCount: number, totalThroughput: number): void {
    const elapsed = (Date.now() - this.startTime) / 1000;
    const avgTimePerIteration = elapsed / iteration;
    const estimatedRemaining = (100 - iteration) * avgTimePerIteration;
    const avgThroughput = successCount > 0 ? totalThroughput / successCount : 0;
    
    console.log(`\n📈 Streaming Progress (${iteration}/100):`);
    console.log(`  Success rate: ${(successCount / iteration * 100).toFixed(1)}%`);
    console.log(`  Gates passed: ${(gatesPassedCount / iteration * 100).toFixed(1)}%`);
    console.log(`  Avg throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Avg time per iteration: ${avgTimePerIteration.toFixed(2)}s`);
    console.log(`  Estimated remaining: ${(estimatedRemaining / 60).toFixed(1)} minutes`);
  }

  private async generateStreamingReport(
    totalTime: number, 
    successCount: number, 
    gatesPassedCount: number, 
    totalThroughput: number,
    totalStreamingLatency: number
  ): Promise<void> {
    console.log('\n🎯 STREAMING TEST RESULTS');
    console.log('='.repeat(70));
    
    // Overall statistics
    console.log(`Total operations: 100`);
    console.log(`Successful operations: ${successCount} (${(successCount / 100 * 100).toFixed(1)}%)`);
    console.log(`Gates passed operations: ${gatesPassedCount} (${(gatesPassedCount / 100 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per operation: ${(totalTime / 100).toFixed(2)} seconds`);

    // Streaming performance statistics
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

      console.log('\n📊 Streaming Performance Averages:');
      console.log(`  Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Streaming Latency: ${avgStreamingLatency.toFixed(2)} ms`);
      console.log(`  Transport p99: ${avgTransportP99.toFixed(2)} ms`);
      console.log(`  Storage p99: ${avgStorageP99.toFixed(2)} ms`);
      console.log(`  Compute p99: ${avgComputeP99.toFixed(2)} ms`);
      console.log(`  E2E p99: ${avgE2eP99.toFixed(2)} ms`);
      console.log(`  Window closure: ${avgWindowClosure.toFixed(2)}%`);
      console.log(`  Reject rate: ${avgRejectRate.toFixed(2)}%`);
    }

    // Streaming efficiency metrics
    const streamingEfficiency = (successCount / 100) * 100;
    const throughputEfficiency = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    
    console.log('\n🚀 Streaming Efficiency:');
    console.log(`  Operation success rate: ${streamingEfficiency.toFixed(1)}%`);
    console.log(`  Throughput target achievement: ${throughputEfficiency.toFixed(1)}%`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/100-matrices-streaming-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        totalOperations: 100,
        successfulOperations: successCount,
        gatesPassedOperations: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerOperation: totalTime / 100,
        streamingEfficiency,
        throughputEfficiency
      },
      performance: successfulResults.length > 0 ? {
        averageThroughput: totalThroughput / successfulResults.length,
        averageStreamingLatency: totalStreamingLatency / successfulResults.length,
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

    // Final streaming verdict
    console.log('\n🏁 STREAMING TEST VERDICT:');
    if (successCount >= 95 && gatesPassedCount >= 90 && throughputEfficiency >= 80) {
      console.log('✅ EXCELLENT: Streaming test passed with high success, gates, and throughput rates');
    } else if (successCount >= 85 && gatesPassedCount >= 75 && throughputEfficiency >= 60) {
      console.log('✅ GOOD: Streaming test passed with acceptable performance');
    } else if (successCount >= 70) {
      console.log('⚠️  MARGINAL: Streaming test completed but with concerning performance');
    } else {
      console.log('❌ POOR: Streaming test failed with high failure rates');
    }

    // Throughput achievement summary
    const throughputAchievement = successfulResults.length > 0 ? 
      (successfulResults.filter(r => r.throughput >= 25.0).length / successfulResults.length) * 100 : 0;
    
    console.log(`\n🎯 Throughput Achievement: ${throughputAchievement.toFixed(1)}% of operations met ≥25 Gbit/s target`);
  }
}

// Main execution
async function main() {
  const test = new StreamingMatrix100Test();
  
  try {
    await test.run100StreamingMatrices();
    console.log('\n🎉 100 streaming matrix operations test completed!');
  } catch (error) {
    console.error('❌ Streaming test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

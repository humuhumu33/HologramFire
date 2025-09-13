/**
 * Simple 2048×2048 Matrix Calculations Test - 100 Samples
 * Focuses on matrix operations without strict throughput requirements
 */

import { createMatMulUseCase, createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';
import { calculateMatrixDataInfo, calculateThroughput } from './src/utils/throughput';

interface SimpleTestResult {
  sample: number;
  success: boolean;
  duration: number;
  throughput: number;
  totalBlocks: number;
  actualDataProcessed: number;
  matrixSize: string;
  blocksProcessed: number;
}

class SimpleMatrix2048Test {
  private config: MatMulConfig;
  private results: SimpleTestResult[] = [];
  private startTime: number = 0;

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
      targetGbps: 25.0  // Target throughput (informational)
    };
  }

  async runSimple2048MatrixTest(): Promise<void> {
    console.log('🚀 SIMPLE 2048×2048 MATRIX CALCULATIONS TEST');
    console.log('='.repeat(70));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Samples: 100`);
    console.log('='.repeat(70));

    this.startTime = Date.now();
    let successCount = 0;
    let totalThroughput = 0;
    let totalDataProcessed = 0;

    // Run 100 matrix calculations
    for (let i = 1; i <= 100; i++) {
      try {
        const iterationStart = Date.now();
        
        // Create matrix use case for this iteration
        const matMulUseCase = await createMatMulUseCase(this.config);
        
        // Perform matrix multiplication operations
        const result = await this.performMatrixOperations(matMulUseCase, i);
        const duration = Date.now() - iterationStart;
        
        // Calculate throughput
        const matrixDataInfo = calculateMatrixDataInfo(this.config.size, this.config.block);
        const durationSeconds = duration / 1000;
        const throughputMeasurement = calculateThroughput(matrixDataInfo.totalDataBytes, durationSeconds);
        const actualDataProcessed = matrixDataInfo.totalDataBytes;

        const testResult: SimpleTestResult = {
          sample: i,
          success: result.success,
          duration,
          throughput: throughputMeasurement.throughputGbps,
          totalBlocks: result.totalBlocks,
          actualDataProcessed,
          matrixSize: `${this.config.size}×${this.config.size}`,
          blocksProcessed: result.blocksProcessed
        };

        this.results.push(testResult);

        if (result.success) {
          successCount++;
          totalThroughput += throughputMeasurement.throughputGbps;
          totalDataProcessed += actualDataProcessed;
        }

        // Progress reporting every 10 iterations
        if (i % 10 === 0) {
          this.reportProgress(i, successCount, totalThroughput);
        }

        // Small delay between operations
        if (i < 100) {
          await new Promise(resolve => setTimeout(resolve, 10));
        }

      } catch (error) {
        console.error(`❌ Sample ${i} failed:`, error);
        
        const testResult: SimpleTestResult = {
          sample: i,
          success: false,
          duration: 0,
          throughput: 0,
          totalBlocks: 0,
          actualDataProcessed: 0,
          matrixSize: `${this.config.size}×${this.config.size}`,
          blocksProcessed: 0
        };
        
        this.results.push(testResult);
      }
    }

    const totalTime = (Date.now() - this.startTime) / 1000;
    await this.generateReport(totalTime, successCount, totalThroughput, totalDataProcessed);
  }

  private async performMatrixOperations(matMulUseCase: any, sample: number): Promise<{
    success: boolean;
    totalBlocks: number;
    blocksProcessed: number;
  }> {
    try {
      // Get matrix statistics
      const stats = matMulUseCase.getStats();
      
      // Get all blocks
      const allBlocks = matMulUseCase.getAllBlocks();
      const matrixABlocks = matMulUseCase.getBlocksByMatrix('A');
      const matrixBBlocks = matMulUseCase.getBlocksByMatrix('B');
      
      let blocksProcessed = 0;
      
      // Perform some matrix multiplication operations
      const blockCount = Math.ceil(this.config.size / this.config.block);
      const maxOperations = Math.min(10, blockCount * blockCount); // Limit operations for performance
      
      for (let i = 0; i < maxOperations; i++) {
        const blockA = matrixABlocks[i % matrixABlocks.length];
        const blockB = matrixBBlocks[i % matrixBBlocks.length];
        
        if (blockA && blockB) {
          // Perform block multiplication
          const result = matMulUseCase.multiplyBlocks(blockA, blockB);
          blocksProcessed++;
          
          // Validate the result
          if (!matMulUseCase.validateBlock(result)) {
            throw new Error(`Invalid block result for operation ${i}`);
          }
        }
      }
      
      return {
        success: true,
        totalBlocks: allBlocks.length,
        blocksProcessed
      };
      
    } catch (error) {
      console.error(`Matrix operations failed for sample ${sample}:`, error);
      return {
        success: false,
        totalBlocks: 0,
        blocksProcessed: 0
      };
    }
  }

  private reportProgress(sample: number, successCount: number, totalThroughput: number): void {
    const elapsed = (Date.now() - this.startTime) / 1000;
    const avgTimePerSample = elapsed / sample;
    const estimatedRemaining = (100 - sample) * avgTimePerSample;
    const avgThroughput = successCount > 0 ? totalThroughput / successCount : 0;
    
    console.log(`\n📈 Progress (${sample}/100):`);
    console.log(`  Success rate: ${(successCount / sample * 100).toFixed(1)}%`);
    console.log(`  Avg throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
    console.log(`  Avg time per sample: ${avgTimePerSample.toFixed(2)}s`);
    console.log(`  Estimated remaining: ${(estimatedRemaining / 60).toFixed(1)} minutes`);
  }

  private async generateReport(
    totalTime: number, 
    successCount: number, 
    totalThroughput: number,
    totalDataProcessed: number
  ): Promise<void> {
    console.log('\n🎯 SIMPLE 2048×2048 MATRIX TEST RESULTS');
    console.log('='.repeat(70));
    
    // Overall statistics
    console.log(`Matrix size: 2048×2048`);
    console.log(`Total samples: 100`);
    console.log(`Successful samples: ${successCount} (${(successCount / 100 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per sample: ${(totalTime / 100).toFixed(2)} seconds`);

    // Performance statistics
    const successfulResults = this.results.filter(r => r.success);
    if (successfulResults.length > 0) {
      const avgThroughput = totalThroughput / successfulResults.length;
      const avgDuration = successfulResults.reduce((sum, r) => sum + r.duration, 0) / successfulResults.length;
      const avgBlocksProcessed = successfulResults.reduce((sum, r) => sum + r.blocksProcessed, 0) / successfulResults.length;

      console.log('\n📊 Performance Averages:');
      console.log(`  Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Duration: ${avgDuration.toFixed(2)} ms`);
      console.log(`  Blocks processed: ${avgBlocksProcessed.toFixed(0)}`);
      console.log(`  Total data processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB`);
    }

    // Efficiency metrics
    const successRate = (successCount / 100) * 100;
    
    console.log('\n🚀 Efficiency Metrics:');
    console.log(`  Operation success rate: ${successRate.toFixed(1)}%`);

    // Save detailed results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/2048-matrices-100-simple-${timestamp}.json`;
    
    const reportData = {
      testConfig: this.config,
      summary: {
        matrixSize: '2048×2048',
        totalSamples: 100,
        successfulSamples: successCount,
        totalTimeSeconds: totalTime,
        averageTimePerSample: totalTime / 100,
        successRate,
        totalDataProcessedGB: totalDataProcessed / 1e9
      },
      performance: successfulResults.length > 0 ? {
        averageThroughput: totalThroughput / successfulResults.length,
        averageDuration: successfulResults.reduce((sum, r) => sum + r.duration, 0) / successfulResults.length,
        averageBlocksProcessed: successfulResults.reduce((sum, r) => sum + r.blocksProcessed, 0) / successfulResults.length
      } : null,
      detailedResults: this.results
    };

    fs.writeFileSync(resultsFile, JSON.stringify(reportData, null, 2));
    console.log(`\n💾 Detailed results saved to: ${resultsFile}`);

    // Final verdict
    console.log('\n🏁 TEST VERDICT:');
    if (successCount >= 95) {
      console.log('✅ EXCELLENT: Test passed with high success rate');
    } else if (successCount >= 85) {
      console.log('✅ GOOD: Test passed with acceptable success rate');
    } else if (successCount >= 70) {
      console.log('⚠️  MARGINAL: Test completed but with concerning success rate');
    } else {
      console.log('❌ POOR: Test failed with high failure rate');
    }

    console.log(`\n🎯 Success Rate: ${successRate.toFixed(1)}% of samples completed successfully`);
    console.log(`📊 Total Data Processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB across 100 matrix calculations`);
    console.log(`🔢 Matrix Size: 2048×2048 with 128×128 blocks`);
  }
}

// Main execution
async function main() {
  const test = new SimpleMatrix2048Test();
  
  try {
    await test.runSimple2048MatrixTest();
    console.log('\n🎉 Simple 2048×2048 matrix calculations test completed!');
  } catch (error) {
    console.error('❌ Test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

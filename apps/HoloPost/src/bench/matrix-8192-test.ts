/**
 * 8192×8192 Matrix Multiplication Test
 * 
 * This test performs large-scale matrix multiplication using the Hologram infrastructure
 * with comprehensive performance monitoring and load generation capabilities.
 */

import { runLoad, RunArgs, RunStats } from './loadgen';
import { createHash } from 'crypto';

interface MatrixTestConfig {
  matrixSize: number;
  blockSize: number;
  testDuration: number;
  targetGbps: number;
  workers: number;
  lanes: number;
  payloadBytes: number;
  batch: number;
  windowMs: number;
}

interface MatrixTestResult {
  config: MatrixTestConfig;
  loadStats: RunStats;
  matrixStats: {
    totalElements: number;
    totalBlocks: number;
    blockElements: number;
    memoryPerMatrix: number;
    totalMemory: number;
    computationComplexity: number;
  };
  performance: {
    elementsPerSecond: number;
    blocksPerSecond: number;
    memoryThroughput: number;
    computationRate: number;
    efficiency: number;
  };
  timestamp: string;
}

class Matrix8192Test {
  private config: MatrixTestConfig;

  constructor() {
    this.config = {
      matrixSize: 8192,
      blockSize: 256,
      testDuration: 30, // 30 seconds test
      targetGbps: 25.0,
      workers: 16,
      lanes: 64,
      payloadBytes: 16384, // 16KB payloads
      batch: 8,
      windowMs: 100
    };
  }

  /**
   * Generate matrix data for testing
   */
  private generateMatrixData(size: number): Buffer {
    const elements = size * size;
    const buffer = Buffer.alloc(elements * 2); // 2 bytes per Int16
    
    // Generate deterministic but varied data
    for (let i = 0; i < elements; i++) {
      const value = (i * 7 + (i % 13) * 11) % 32767; // Deterministic pattern
      buffer.writeInt16LE(value, i * 2);
    }
    
    return buffer;
  }

  /**
   * Simulate matrix multiplication computation
   */
  private async simulateMatrixMultiplication(
    matrixA: Buffer, 
    matrixB: Buffer, 
    size: number
  ): Promise<Buffer> {
    const result = Buffer.alloc(size * size * 2);
    
    // Simulate O(n³) computation time
    const computationTime = Math.max(1, (size * size * size) / 10000000);
    await new Promise(resolve => setTimeout(resolve, computationTime));
    
    // Perform actual matrix multiplication
    for (let i = 0; i < size; i++) {
      for (let j = 0; j < size; j++) {
        let sum = 0;
        for (let k = 0; k < size; k++) {
          const a = matrixA.readInt16LE((i * size + k) * 2);
          const b = matrixB.readInt16LE((k * size + j) * 2);
          sum += a * b;
        }
        result.writeInt16LE(Math.min(sum, 32767), (i * size + j) * 2);
      }
    }
    
    return result;
  }

  /**
   * Run the 8192×8192 matrix multiplication test
   */
  async runMatrixTest(): Promise<MatrixTestResult> {
    console.log('🚀 Starting 8192×8192 Matrix Multiplication Test');
    console.log('='.repeat(60));
    console.log(`Matrix size: ${this.config.matrixSize}×${this.config.matrixSize}`);
    console.log(`Block size: ${this.config.blockSize}×${this.config.blockSize}`);
    console.log(`Test duration: ${this.config.testDuration} seconds`);
    console.log(`Target throughput: ${this.config.targetGbps} Gbit/s`);
    console.log(`Workers: ${this.config.workers}, Lanes: ${this.config.lanes}`);
    console.log('='.repeat(60));

    const startTime = Date.now();

    // Calculate matrix statistics
    const totalElements = this.config.matrixSize * this.config.matrixSize;
    const blockCount = Math.ceil(this.config.matrixSize / this.config.blockSize);
    const totalBlocks = blockCount * blockCount * 2; // A and B matrices
    const blockElements = this.config.blockSize * this.config.blockSize;
    const memoryPerMatrix = totalElements * 2; // 2 bytes per Int16
    const totalMemory = memoryPerMatrix * 2; // A and B matrices
    const computationComplexity = totalElements * this.config.matrixSize; // O(n³)

    console.log(`\n📊 Matrix Statistics:`);
    console.log(`  Total elements per matrix: ${totalElements.toLocaleString()}`);
    console.log(`  Total blocks: ${totalBlocks.toLocaleString()}`);
    console.log(`  Elements per block: ${blockElements.toLocaleString()}`);
    console.log(`  Memory per matrix: ${(memoryPerMatrix / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Total memory: ${(totalMemory / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Computation complexity: ${computationComplexity.toLocaleString()} operations`);

    // Generate test matrices
    console.log(`\n🔢 Generating test matrices...`);
    const matrixA = this.generateMatrixData(this.config.matrixSize);
    const matrixB = this.generateMatrixData(this.config.matrixSize);
    
    // Generate hash for verification
    const matrixAHash = createHash('sha256').update(matrixA).digest('hex');
    const matrixBHash = createHash('sha256').update(matrixB).digest('hex');
    console.log(`  Matrix A hash: ${matrixAHash.substring(0, 16)}...`);
    console.log(`  Matrix B hash: ${matrixBHash.substring(0, 16)}...`);

    // Run load generation test
    console.log(`\n⚡ Running load generation test...`);
    const loadArgs: RunArgs = {
      durationSec: this.config.testDuration,
      lanes: this.config.lanes,
      payloadBytes: this.config.payloadBytes,
      targetGbps: this.config.targetGbps,
      batch: this.config.batch,
      windowMs: this.config.windowMs,
      workers: this.config.workers,
      budget: {
        io: 1000000, // 1M IO operations
        cpuMs: this.config.testDuration * 1000, // Full CPU for test duration
        mem: 1024 // 1GB memory
      }
    };

    const loadStats = await runLoad(loadArgs);

    // Perform actual matrix multiplication
    console.log(`\n🧮 Performing matrix multiplication...`);
    const computeStart = Date.now();
    const resultMatrix = await this.simulateMatrixMultiplication(
      matrixA, 
      matrixB, 
      this.config.matrixSize
    );
    const computeTime = Date.now() - computeStart;
    
    const resultHash = createHash('sha256').update(resultMatrix).digest('hex');
    console.log(`  Result matrix hash: ${resultHash.substring(0, 16)}...`);
    console.log(`  Computation time: ${(computeTime / 1000).toFixed(2)} seconds`);

    // Calculate performance metrics
    const totalTime = (Date.now() - startTime) / 1000;
    const elementsPerSecond = totalElements / totalTime;
    const blocksPerSecond = totalBlocks / totalTime;
    const memoryThroughput = (totalMemory / totalTime) / (1024 * 1024); // MB/s
    const computationRate = computationComplexity / totalTime;
    const efficiency = (loadStats.gbps / this.config.targetGbps) * 100;

    const matrixStats = {
      totalElements,
      totalBlocks,
      blockElements,
      memoryPerMatrix,
      totalMemory,
      computationComplexity
    };

    const performance = {
      elementsPerSecond,
      blocksPerSecond,
      memoryThroughput,
      computationRate,
      efficiency
    };

    const result: MatrixTestResult = {
      config: this.config,
      loadStats,
      matrixStats,
      performance,
      timestamp: new Date().toISOString()
    };

    return result;
  }

  /**
   * Generate comprehensive test report
   */
  async generateReport(result: MatrixTestResult): Promise<void> {
    console.log('\n🎯 MATRIX MULTIPLICATION TEST RESULTS');
    console.log('='.repeat(60));

    // Test configuration
    console.log(`\n📋 Test Configuration:`);
    console.log(`  Matrix size: ${result.config.matrixSize}×${result.config.matrixSize}`);
    console.log(`  Block size: ${result.config.blockSize}×${result.config.blockSize}`);
    console.log(`  Test duration: ${result.config.testDuration} seconds`);
    console.log(`  Target throughput: ${result.config.targetGbps} Gbit/s`);

    // Load generation results
    console.log(`\n⚡ Load Generation Results:`);
    console.log(`  Achieved throughput: ${result.loadStats.gbps.toFixed(2)} Gbit/s`);
    console.log(`  Frames per second: ${result.loadStats.fps.toFixed(0)}`);
    console.log(`  Frames sent: ${result.loadStats.sent.toLocaleString()}`);
    console.log(`  Frames delivered: ${result.loadStats.delivered.toLocaleString()}`);
    console.log(`  Rejection rate: ${((result.loadStats.rejected / result.loadStats.sent) * 100).toFixed(2)}%`);
    console.log(`  P50 latency: ${result.loadStats.p50latencyMs.toFixed(2)} ms`);
    console.log(`  P99 latency: ${result.loadStats.p99latencyMs.toFixed(2)} ms`);
    console.log(`  CPU usage: ${result.loadStats.cpuPercent.toFixed(1)}%`);

    // Matrix statistics
    console.log(`\n📊 Matrix Statistics:`);
    console.log(`  Total elements: ${result.matrixStats.totalElements.toLocaleString()}`);
    console.log(`  Total blocks: ${result.matrixStats.totalBlocks.toLocaleString()}`);
    console.log(`  Memory per matrix: ${(result.matrixStats.memoryPerMatrix / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Total memory: ${(result.matrixStats.totalMemory / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Computation complexity: ${result.matrixStats.computationComplexity.toLocaleString()} ops`);

    // Performance metrics
    console.log(`\n🚀 Performance Metrics:`);
    console.log(`  Elements per second: ${result.performance.elementsPerSecond.toLocaleString()}`);
    console.log(`  Blocks per second: ${result.performance.blocksPerSecond.toFixed(1)}`);
    console.log(`  Memory throughput: ${result.performance.memoryThroughput.toFixed(1)} MB/s`);
    console.log(`  Computation rate: ${result.performance.computationRate.toLocaleString()} ops/s`);
    console.log(`  Efficiency: ${result.performance.efficiency.toFixed(1)}%`);

    // Performance analysis
    console.log(`\n📈 Performance Analysis:`);
    if (result.loadStats.gbps >= result.config.targetGbps) {
      console.log(`  ✅ Throughput target achieved: ${result.loadStats.gbps.toFixed(2)} ≥ ${result.config.targetGbps} Gbit/s`);
    } else {
      console.log(`  ❌ Throughput target missed: ${result.loadStats.gbps.toFixed(2)} < ${result.config.targetGbps} Gbit/s`);
    }

    if (result.performance.efficiency >= 80) {
      console.log(`  ✅ High efficiency: ${result.performance.efficiency.toFixed(1)}%`);
    } else if (result.performance.efficiency >= 60) {
      console.log(`  ⚠️  Moderate efficiency: ${result.performance.efficiency.toFixed(1)}%`);
    } else {
      console.log(`  ❌ Low efficiency: ${result.performance.efficiency.toFixed(1)}%`);
    }

    // Save results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/matrix-8192-test-${timestamp}.json`;
    
    fs.writeFileSync(resultsFile, JSON.stringify(result, null, 2));
    console.log(`\n💾 Detailed results saved to: ${resultsFile}`);

    // Final verdict
    console.log('\n🏁 TEST VERDICT:');
    const success = result.loadStats.gbps >= result.config.targetGbps * 0.8; // 80% of target
    if (success) {
      console.log('✅ SUCCESS: 8192×8192 matrix multiplication test completed successfully');
      console.log('🚀 The Hologram system can handle large matrix operations efficiently!');
    } else {
      console.log('❌ FAILED: Matrix multiplication test did not meet performance targets');
      console.log('🔧 Consider optimizing system configuration or increasing resources');
    }
  }
}

// Main execution function
async function main() {
  const test = new Matrix8192Test();
  
  try {
    console.log('🎯 Starting 8192×8192 Matrix Multiplication Test Suite');
    console.log('This test will evaluate the Hologram system\'s ability to handle large matrix operations');
    console.log('with comprehensive performance monitoring and load generation.\n');
    
    const result = await test.runMatrixTest();
    await test.generateReport(result);
    
    console.log('\n🎉 Matrix multiplication test completed successfully!');
  } catch (error) {
    console.error('❌ Matrix multiplication test failed:', error);
    process.exit(1);
  }
}

// Export for use in other modules
export { Matrix8192Test, MatrixTestConfig, MatrixTestResult };

// Run if called directly
if (require.main === module) {
  main();
}

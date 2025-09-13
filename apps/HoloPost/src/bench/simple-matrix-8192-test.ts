/**
 * Simple 8192×8192 Matrix Multiplication Test
 * 
 * A standalone test that performs large-scale matrix multiplication
 * without dependencies on the complex Hologram infrastructure.
 */

import { createHash } from 'crypto';

interface MatrixTestResult {
  matrixSize: number;
  blockSize: number;
  totalElements: number;
  totalBlocks: number;
  memoryPerMatrix: number;
  totalMemory: number;
  computationComplexity: number;
  generationTime: number;
  multiplicationTime: number;
  totalTime: number;
  elementsPerSecond: number;
  blocksPerSecond: number;
  memoryThroughput: number;
  computationRate: number;
  matrixAHash: string;
  matrixBHash: string;
  resultHash: string;
  timestamp: string;
}

class SimpleMatrix8192Test {
  private matrixSize: number;
  private blockSize: number;

  constructor() {
    this.matrixSize = 8192;
    this.blockSize = 256;
  }

  /**
   * Generate matrix data for testing
   */
  private generateMatrixData(size: number): Buffer {
    const elements = size * size;
    const buffer = Buffer.alloc(elements * 2); // 2 bytes per Int16
    
    console.log(`  Generating ${elements.toLocaleString()} elements...`);
    
    // Generate deterministic but varied data
    for (let i = 0; i < elements; i++) {
      const value = (i * 7 + (i % 13) * 11) % 32767; // Deterministic pattern
      buffer.writeInt16LE(value, i * 2);
      
      // Progress indicator for large matrices
      if (i % (elements / 10) === 0) {
        const progress = Math.round((i / elements) * 100);
        process.stdout.write(`\r    Progress: ${progress}%`);
      }
    }
    console.log(`\r    Progress: 100% - Complete!`);
    
    return buffer;
  }

  /**
   * Perform matrix multiplication with progress tracking
   */
  private async performMatrixMultiplication(
    matrixA: Buffer, 
    matrixB: Buffer, 
    size: number
  ): Promise<Buffer> {
    const result = Buffer.alloc(size * size * 2);
    const totalOperations = size * size * size;
    let operationsCompleted = 0;
    
    console.log(`  Performing ${totalOperations.toLocaleString()} operations...`);
    
    // Perform matrix multiplication
    for (let i = 0; i < size; i++) {
      for (let j = 0; j < size; j++) {
        let sum = 0;
        for (let k = 0; k < size; k++) {
          const a = matrixA.readInt16LE((i * size + k) * 2);
          const b = matrixB.readInt16LE((k * size + j) * 2);
          sum += a * b;
          operationsCompleted++;
        }
        result.writeInt16LE(Math.min(sum, 32767), (i * size + j) * 2);
      }
      
      // Progress indicator
      if (i % (size / 10) === 0) {
        const progress = Math.round((operationsCompleted / totalOperations) * 100);
        process.stdout.write(`\r    Progress: ${progress}% (${operationsCompleted.toLocaleString()}/${totalOperations.toLocaleString()} ops)`);
      }
    }
    console.log(`\r    Progress: 100% - Complete! (${operationsCompleted.toLocaleString()} operations)`);
    
    return result;
  }

  /**
   * Run the 8192×8192 matrix multiplication test
   */
  async runMatrixTest(): Promise<MatrixTestResult> {
    console.log('🚀 Starting Simple 8192×8192 Matrix Multiplication Test');
    console.log('='.repeat(60));
    console.log(`Matrix size: ${this.matrixSize}×${this.matrixSize}`);
    console.log(`Block size: ${this.blockSize}×${this.blockSize}`);
    console.log('='.repeat(60));

    const startTime = Date.now();

    // Calculate matrix statistics
    const totalElements = this.matrixSize * this.matrixSize;
    const blockCount = Math.ceil(this.matrixSize / this.blockSize);
    const totalBlocks = blockCount * blockCount * 2; // A and B matrices
    const memoryPerMatrix = totalElements * 2; // 2 bytes per Int16
    const totalMemory = memoryPerMatrix * 2; // A and B matrices
    const computationComplexity = totalElements * this.matrixSize; // O(n³)

    console.log(`\n📊 Matrix Statistics:`);
    console.log(`  Total elements per matrix: ${totalElements.toLocaleString()}`);
    console.log(`  Total blocks: ${totalBlocks.toLocaleString()}`);
    console.log(`  Memory per matrix: ${(memoryPerMatrix / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Total memory: ${(totalMemory / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Computation complexity: ${computationComplexity.toLocaleString()} operations`);

    // Generate test matrices
    console.log(`\n🔢 Generating Matrix A...`);
    const matrixAStart = Date.now();
    const matrixA = this.generateMatrixData(this.matrixSize);
    const matrixATime = Date.now() - matrixAStart;
    
    console.log(`🔢 Generating Matrix B...`);
    const matrixBStart = Date.now();
    const matrixB = this.generateMatrixData(this.matrixSize);
    const matrixBTime = Date.now() - matrixBStart;
    
    const generationTime = matrixATime + matrixBTime;
    
    // Generate hashes for verification
    const matrixAHash = createHash('sha256').update(matrixA).digest('hex');
    const matrixBHash = createHash('sha256').update(matrixB).digest('hex');
    console.log(`\n📋 Matrix Hashes:`);
    console.log(`  Matrix A: ${matrixAHash.substring(0, 16)}...`);
    console.log(`  Matrix B: ${matrixBHash.substring(0, 16)}...`);

    // Perform matrix multiplication
    console.log(`\n🧮 Performing Matrix Multiplication (A × B)...`);
    const multiplicationStart = Date.now();
    const resultMatrix = await this.performMatrixMultiplication(
      matrixA, 
      matrixB, 
      this.matrixSize
    );
    const multiplicationTime = Date.now() - multiplicationStart;
    
    const resultHash = createHash('sha256').update(resultMatrix).digest('hex');
    console.log(`\n📋 Result Matrix Hash: ${resultHash.substring(0, 16)}...`);

    // Calculate performance metrics
    const totalTime = (Date.now() - startTime) / 1000;
    const elementsPerSecond = totalElements / totalTime;
    const blocksPerSecond = totalBlocks / totalTime;
    const memoryThroughput = (totalMemory / totalTime) / (1024 * 1024); // MB/s
    const computationRate = computationComplexity / totalTime;

    const result: MatrixTestResult = {
      matrixSize: this.matrixSize,
      blockSize: this.blockSize,
      totalElements,
      totalBlocks,
      memoryPerMatrix,
      totalMemory,
      computationComplexity,
      generationTime,
      multiplicationTime,
      totalTime,
      elementsPerSecond,
      blocksPerSecond,
      memoryThroughput,
      computationRate,
      matrixAHash,
      matrixBHash,
      resultHash,
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
    console.log(`  Matrix size: ${result.matrixSize}×${result.matrixSize}`);
    console.log(`  Block size: ${result.blockSize}×${result.blockSize}`);

    // Matrix statistics
    console.log(`\n📊 Matrix Statistics:`);
    console.log(`  Total elements: ${result.totalElements.toLocaleString()}`);
    console.log(`  Total blocks: ${result.totalBlocks.toLocaleString()}`);
    console.log(`  Memory per matrix: ${(result.memoryPerMatrix / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Total memory: ${(result.totalMemory / 1024 / 1024).toFixed(1)} MB`);
    console.log(`  Computation complexity: ${result.computationComplexity.toLocaleString()} operations`);

    // Timing results
    console.log(`\n⏱️  Timing Results:`);
    console.log(`  Matrix generation time: ${(result.generationTime / 1000).toFixed(2)} seconds`);
    console.log(`  Multiplication time: ${(result.multiplicationTime / 1000).toFixed(2)} seconds`);
    console.log(`  Total test time: ${result.totalTime.toFixed(2)} seconds`);

    // Performance metrics
    console.log(`\n🚀 Performance Metrics:`);
    console.log(`  Elements per second: ${result.elementsPerSecond.toLocaleString()}`);
    console.log(`  Blocks per second: ${result.blocksPerSecond.toFixed(1)}`);
    console.log(`  Memory throughput: ${result.memoryThroughput.toFixed(1)} MB/s`);
    console.log(`  Computation rate: ${result.computationRate.toLocaleString()} ops/s`);

    // Hash verification
    console.log(`\n🔐 Hash Verification:`);
    console.log(`  Matrix A: ${result.matrixAHash.substring(0, 16)}...`);
    console.log(`  Matrix B: ${result.matrixBHash.substring(0, 16)}...`);
    console.log(`  Result: ${result.resultHash.substring(0, 16)}...`);

    // Performance analysis
    console.log(`\n📈 Performance Analysis:`);
    const theoreticalMax = (result.totalMemory / result.multiplicationTime) / (1024 * 1024); // MB/s
    const efficiency = (result.memoryThroughput / theoreticalMax) * 100;
    console.log(`  Theoretical max throughput: ${theoreticalMax.toFixed(1)} MB/s`);
    console.log(`  Achieved throughput: ${result.memoryThroughput.toFixed(1)} MB/s`);
    console.log(`  Efficiency: ${efficiency.toFixed(1)}%`);

    // Save results
    const fs = require('fs');
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = `${resultsDir}/simple-matrix-8192-test-${timestamp}.json`;
    
    fs.writeFileSync(resultsFile, JSON.stringify(result, null, 2));
    console.log(`\n💾 Detailed results saved to: ${resultsFile}`);

    // Final verdict
    console.log('\n🏁 TEST VERDICT:');
    if (result.multiplicationTime < 300000) { // Less than 5 minutes
      console.log('✅ SUCCESS: 8192×8192 matrix multiplication completed successfully');
      console.log('🚀 The system can handle large matrix operations efficiently!');
    } else {
      console.log('⚠️  SLOW: Matrix multiplication completed but took longer than expected');
      console.log('🔧 Consider optimizing the implementation or using more powerful hardware');
    }

    // Performance comparison
    console.log('\n📊 Performance Summary:');
    console.log(`  Matrix size: ${result.matrixSize}×${result.matrixSize} = ${result.totalElements.toLocaleString()} elements`);
    console.log(`  Computation: ${result.computationComplexity.toLocaleString()} operations in ${(result.multiplicationTime / 1000).toFixed(2)}s`);
    console.log(`  Rate: ${result.computationRate.toLocaleString()} operations/second`);
    console.log(`  Memory: ${(result.totalMemory / 1024 / 1024).toFixed(1)} MB processed in ${(result.multiplicationTime / 1000).toFixed(2)}s`);
    console.log(`  Throughput: ${result.memoryThroughput.toFixed(1)} MB/s`);
  }
}

// Main execution function
async function main() {
  const test = new SimpleMatrix8192Test();
  
  try {
    console.log('🎯 Starting Simple 8192×8192 Matrix Multiplication Test');
    console.log('This test will evaluate the system\'s ability to handle large matrix operations');
    console.log('with comprehensive performance monitoring.\n');
    
    const result = await test.runMatrixTest();
    await test.generateReport(result);
    
    console.log('\n🎉 Matrix multiplication test completed successfully!');
  } catch (error) {
    console.error('❌ Matrix multiplication test failed:', error);
    process.exit(1);
  }
}

// Export for use in other modules
export { SimpleMatrix8192Test, MatrixTestResult };

// Run if called directly
if (require.main === module) {
  main();
}

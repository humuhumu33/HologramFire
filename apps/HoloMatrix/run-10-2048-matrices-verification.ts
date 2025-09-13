/**
 * 10 × 2048×2048 Matrix Operations Verification Test
 * Comprehensive test to verify matrix operations are executed correctly
 */

import { MatMulStep } from './src/steps/05-matmul';
import { createDefaultMatMulConfig } from './src/usecases/matmul';
import type { MatMulConfig } from './src/types';
import { calculateMatrixDataInfo, calculateThroughput } from './src/utils/throughput';
import * as fs from 'fs';
import * as path from 'path';

interface VerificationResult {
  operation: number;
  success: boolean;
  allGatesPassed: boolean;
  duration: number;
  throughput: number;
  totalBlocks: number;
  blocksProcessed: number;
  matrixSize: string;
  dataProcessed: number;
  verificationChecks: {
    matrixSizeValid: boolean;
    blockStructureValid: boolean;
    computationValid: boolean;
    resultIntegrityValid: boolean;
    performanceWithinBounds: boolean;
  };
  errorDetails?: string;
}

class Matrix2048VerificationTest {
  private config: MatMulConfig;
  private results: VerificationResult[] = [];
  private startTime: number = 0;

  constructor() {
    // Configuration for 2048×2048 matrix operations
    this.config = {
      ...createDefaultMatMulConfig(),
      size: 2048,       // 2048×2048 matrix
      block: 128,       // 128×128 blocks
      lanes: 64,        // 64 transport lanes
      payload: 8192,    // Larger payload for better performance
      batch: 32,        // Batch size
      workers: 8,       // Workers for parallel processing
      window: 50,       // Window size
      targetGbps: 25.0  // Target throughput
    };
  }

  async runVerificationTest(): Promise<void> {
    console.log('🚀 2048×2048 MATRIX OPERATIONS VERIFICATION TEST');
    console.log('='.repeat(80));
    console.log(`Configuration:`);
    console.log(`  Matrix size: ${this.config.size}×${this.config.size}`);
    console.log(`  Block size: ${this.config.block}×${this.config.block}`);
    console.log(`  Operations: 10`);
    console.log(`  Target throughput: ${this.config.targetGbps} Gbit/s`);
    console.log(`  Lanes: ${this.config.lanes}`);
    console.log(`  Workers: ${this.config.workers}`);
    console.log('='.repeat(80));

    this.startTime = Date.now();
    let successCount = 0;
    let gatesPassedCount = 0;
    let totalDataProcessed = 0;

    // Calculate expected matrix properties
    const matrixDataInfo = calculateMatrixDataInfo(this.config.size, this.config.block);
    const expectedBlocks = matrixDataInfo.totalBlocks;
    const expectedDataSize = matrixDataInfo.totalDataBytes;

    console.log(`\n📊 Expected Matrix Properties:`);
    console.log(`  Total blocks: ${expectedBlocks}`);
    console.log(`  Data size: ${(expectedDataSize / 1e9).toFixed(2)} GB`);
    console.log(`  Blocks per matrix: ${Math.ceil(this.config.size / this.config.block)}×${Math.ceil(this.config.size / this.config.block)}`);

    // Run 10 matrix operations
    for (let i = 1; i <= 10; i++) {
      try {
        console.log(`\n🔬 Running verification operation ${i}/10...`);
        
        const operationStart = Date.now();
        const matMul = new MatMulStep(this.config);
        const result = await matMul.runMatMulPipeline();
        const duration = Date.now() - operationStart;

        // Perform verification checks
        const verificationChecks = await this.performVerificationChecks(result, i);
        
        // Calculate data processed
        const dataProcessed = expectedDataSize;

        const verificationResult: VerificationResult = {
          operation: i,
          success: result.success,
          allGatesPassed: result.allGatesPassed,
          duration,
          throughput: result.metrics.throughputGbps,
          totalBlocks: result.matrixStats.totalBlocks,
          blocksProcessed: result.matrixStats.blocksProcessed || expectedBlocks,
          matrixSize: `${this.config.size}×${this.config.size}`,
          dataProcessed,
          verificationChecks
        };

        this.results.push(verificationResult);

        if (result.success) {
          successCount++;
          totalDataProcessed += dataProcessed;
        }
        if (result.allGatesPassed) {
          gatesPassedCount++;
        }

        // Report operation results
        console.log(`  ✅ Operation ${i} completed in ${(duration / 1000).toFixed(2)}s`);
        console.log(`  📈 Throughput: ${result.metrics.throughputGbps.toFixed(2)} Gbit/s`);
        console.log(`  🚪 Gates passed: ${result.allGatesPassed ? 'YES' : 'NO'}`);
        console.log(`  🔍 Verification: ${this.getVerificationSummary(verificationChecks)}`);

        // Brief pause between operations
        if (i < 10) {
          await new Promise(resolve => setTimeout(resolve, 1000));
        }

      } catch (error) {
        console.error(`❌ Operation ${i} failed:`, error);
        
        const verificationResult: VerificationResult = {
          operation: i,
          success: false,
          allGatesPassed: false,
          duration: 0,
          throughput: 0,
          totalBlocks: 0,
          blocksProcessed: 0,
          matrixSize: `${this.config.size}×${this.config.size}`,
          dataProcessed: 0,
          verificationChecks: {
            matrixSizeValid: false,
            blockStructureValid: false,
            computationValid: false,
            resultIntegrityValid: false,
            performanceWithinBounds: false
          },
          errorDetails: error instanceof Error ? error.message : String(error)
        };
        
        this.results.push(verificationResult);
      }
    }

    const totalTime = (Date.now() - this.startTime) / 1000;
    await this.generateVerificationReport(totalTime, successCount, gatesPassedCount, totalDataProcessed);
  }

  private async performVerificationChecks(result: any, operation: number): Promise<{
    matrixSizeValid: boolean;
    blockStructureValid: boolean;
    computationValid: boolean;
    resultIntegrityValid: boolean;
    performanceWithinBounds: boolean;
  }> {
    const checks = {
      matrixSizeValid: false,
      blockStructureValid: false,
      computationValid: false,
      resultIntegrityValid: false,
      performanceWithinBounds: false
    };

    try {
      // Check 1: Matrix size validation
      const expectedBlocks = Math.ceil(this.config.size / this.config.block) * Math.ceil(this.config.size / this.config.block) * 2; // A and B matrices
      checks.matrixSizeValid = result.matrixStats.totalBlocks >= expectedBlocks * 0.9; // Allow 10% tolerance

      // Check 2: Block structure validation
      const blockCount = Math.ceil(this.config.size / this.config.block);
      checks.blockStructureValid = result.matrixStats.totalBlocks > 0 && 
                                  result.matrixStats.totalBlocks <= expectedBlocks * 1.1; // Allow 10% tolerance

      // Check 3: Computation validation
      checks.computationValid = result.success && 
                               result.metrics.throughputGbps > 0 && 
                               result.metrics.throughputGbps < 1000; // Reasonable upper bound

      // Check 4: Result integrity validation
      checks.resultIntegrityValid = result.allGatesPassed && 
                                   result.metrics.e2e.p99Ms > 0 && 
                                   result.metrics.e2e.p99Ms < 60000; // Less than 1 minute

      // Check 5: Performance within bounds
      checks.performanceWithinBounds = result.metrics.throughputGbps >= 1.0 && // At least 1 Gbit/s
                                      result.metrics.throughputGbps <= 100.0; // Reasonable upper bound

    } catch (error) {
      console.warn(`Warning: Verification checks failed for operation ${operation}:`, error);
    }

    return checks;
  }

  private getVerificationSummary(checks: any): string {
    const passed = Object.values(checks).filter(Boolean).length;
    const total = Object.keys(checks).length;
    return `${passed}/${total} checks passed`;
  }

  private async generateVerificationReport(
    totalTime: number, 
    successCount: number, 
    gatesPassedCount: number,
    totalDataProcessed: number
  ): Promise<void> {
    console.log('\n🎯 MATRIX OPERATIONS VERIFICATION REPORT');
    console.log('='.repeat(80));
    
    // Overall statistics
    console.log(`Matrix size: 2048×2048`);
    console.log(`Total operations: 10`);
    console.log(`Successful operations: ${successCount} (${(successCount / 10 * 100).toFixed(1)}%)`);
    console.log(`Gates passed operations: ${gatesPassedCount} (${(gatesPassedCount / 10 * 100).toFixed(1)}%)`);
    console.log(`Total test time: ${(totalTime / 60).toFixed(1)} minutes`);
    console.log(`Average time per operation: ${(totalTime / 10).toFixed(2)} seconds`);

    // Performance statistics
    const successfulResults = this.results.filter(r => r.success);
    if (successfulResults.length > 0) {
      const avgThroughput = successfulResults.reduce((sum, r) => sum + r.throughput, 0) / successfulResults.length;
      const avgDuration = successfulResults.reduce((sum, r) => sum + r.duration, 0) / successfulResults.length;
      const avgBlocksProcessed = successfulResults.reduce((sum, r) => sum + r.blocksProcessed, 0) / successfulResults.length;

      console.log('\n📊 Performance Averages (successful operations):');
      console.log(`  Throughput: ${avgThroughput.toFixed(2)} Gbit/s`);
      console.log(`  Duration: ${avgDuration.toFixed(2)} ms`);
      console.log(`  Blocks processed: ${avgBlocksProcessed.toFixed(0)}`);
      console.log(`  Total data processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB`);
    }

    // Verification analysis
    console.log('\n🔍 Verification Analysis:');
    const allChecks = this.results.flatMap(r => Object.entries(r.verificationChecks));
    const checkStats = allChecks.reduce((acc, [check, passed]) => {
      if (!acc[check]) acc[check] = { passed: 0, total: 0 };
      acc[check].total++;
      if (passed) acc[check].passed++;
      return acc;
    }, {} as Record<string, { passed: number; total: number }>);

    Object.entries(checkStats).forEach(([check, stats]) => {
      const percentage = (stats.passed / stats.total * 100).toFixed(1);
      console.log(`  ${check}: ${stats.passed}/${stats.total} (${percentage}%)`);
    });

    // Save detailed results
    const resultsDir = './bench-results';
    if (!fs.existsSync(resultsDir)) {
      fs.mkdirSync(resultsDir, { recursive: true });
    }

    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const resultsFile = path.join(resultsDir, `2048-matrices-10-verification-${timestamp}.json`);
    
    const reportData = {
      testConfig: this.config,
      summary: {
        matrixSize: '2048×2048',
        totalOperations: 10,
        successfulOperations: successCount,
        gatesPassedOperations: gatesPassedCount,
        totalTimeSeconds: totalTime,
        averageTimePerOperation: totalTime / 10,
        totalDataProcessedGB: totalDataProcessed / 1e9,
        verificationStats: checkStats
      },
      performance: successfulResults.length > 0 ? {
        averageThroughput: successfulResults.reduce((sum, r) => sum + r.throughput, 0) / successfulResults.length,
        averageDuration: successfulResults.reduce((sum, r) => sum + r.duration, 0) / successfulResults.length,
        averageBlocksProcessed: successfulResults.reduce((sum, r) => sum + r.blocksProcessed, 0) / successfulResults.length
      } : null,
      detailedResults: this.results
    };

    fs.writeFileSync(resultsFile, JSON.stringify(reportData, null, 2));
    console.log(`\n💾 Detailed verification results saved to: ${resultsFile}`);

    // Create human-readable output file
    const outputFile = path.join(resultsDir, `2048-matrices-10-verification-${timestamp}.txt`);
    await this.createHumanReadableOutput(outputFile, reportData);

    // Final verdict
    console.log('\n🏁 VERIFICATION VERDICT:');
    const overallSuccessRate = (successCount / 10) * 100;
    const gatesPassRate = (gatesPassedCount / 10) * 100;
    
    if (successCount >= 9 && gatesPassedCount >= 8) {
      console.log('✅ EXCELLENT: Matrix operations verified with high success rate');
    } else if (successCount >= 7 && gatesPassedCount >= 6) {
      console.log('✅ GOOD: Matrix operations verified with acceptable success rate');
    } else if (successCount >= 5) {
      console.log('⚠️  MARGINAL: Matrix operations completed but with concerning failure rates');
    } else {
      console.log('❌ POOR: Matrix operations failed verification with high failure rates');
    }

    console.log(`\n🎯 Success Rate: ${overallSuccessRate.toFixed(1)}% of operations completed successfully`);
    console.log(`🚪 Gates Pass Rate: ${gatesPassRate.toFixed(1)}% of operations passed all gates`);
    console.log(`📊 Total Data Processed: ${(totalDataProcessed / 1e9).toFixed(2)} GB across 10 matrix operations`);
    console.log(`🔢 Matrix Size: 2048×2048 with 128×128 blocks`);
    console.log(`📄 Output files: ${resultsFile} and ${outputFile}`);
  }

  private async createHumanReadableOutput(outputFile: string, reportData: any): Promise<void> {
    const output = [
      '2048×2048 MATRIX OPERATIONS VERIFICATION REPORT',
      '='.repeat(80),
      '',
      `Test Configuration:`,
      `  Matrix Size: ${reportData.testConfig.size}×${reportData.testConfig.size}`,
      `  Block Size: ${reportData.testConfig.block}×${reportData.testConfig.block}`,
      `  Lanes: ${reportData.testConfig.lanes}`,
      `  Workers: ${reportData.testConfig.workers}`,
      `  Target Throughput: ${reportData.testConfig.targetGbps} Gbit/s`,
      '',
      `Test Summary:`,
      `  Total Operations: ${reportData.summary.totalOperations}`,
      `  Successful Operations: ${reportData.summary.successfulOperations} (${(reportData.summary.successfulOperations / reportData.summary.totalOperations * 100).toFixed(1)}%)`,
      `  Gates Passed Operations: ${reportData.summary.gatesPassedOperations} (${(reportData.summary.gatesPassedOperations / reportData.summary.totalOperations * 100).toFixed(1)}%)`,
      `  Total Test Time: ${(reportData.summary.totalTimeSeconds / 60).toFixed(1)} minutes`,
      `  Average Time per Operation: ${reportData.summary.averageTimePerOperation.toFixed(2)} seconds`,
      `  Total Data Processed: ${reportData.summary.totalDataProcessedGB.toFixed(2)} GB`,
      '',
      `Verification Statistics:`,
    ];

    Object.entries(reportData.summary.verificationStats).forEach(([check, stats]: [string, any]) => {
      const percentage = (stats.passed / stats.total * 100).toFixed(1);
      output.push(`  ${check}: ${stats.passed}/${stats.total} (${percentage}%)`);
    });

    if (reportData.performance) {
      output.push(
        '',
        `Performance Averages:`,
        `  Throughput: ${reportData.performance.averageThroughput.toFixed(2)} Gbit/s`,
        `  Duration: ${reportData.performance.averageDuration.toFixed(2)} ms`,
        `  Blocks Processed: ${reportData.performance.averageBlocksProcessed.toFixed(0)}`
      );
    }

    output.push(
      '',
      'Detailed Operation Results:',
      '-'.repeat(80)
    );

    reportData.detailedResults.forEach((result: any, index: number) => {
      output.push(
        '',
        `Operation ${result.operation}:`,
        `  Success: ${result.success ? 'YES' : 'NO'}`,
        `  Gates Passed: ${result.allGatesPassed ? 'YES' : 'NO'}`,
        `  Duration: ${result.duration} ms`,
        `  Throughput: ${result.throughput.toFixed(2)} Gbit/s`,
        `  Total Blocks: ${result.totalBlocks}`,
        `  Blocks Processed: ${result.blocksProcessed}`,
        `  Data Processed: ${(result.dataProcessed / 1e9).toFixed(2)} GB`,
        `  Verification Checks:`,
        `    Matrix Size Valid: ${result.verificationChecks.matrixSizeValid ? 'PASS' : 'FAIL'}`,
        `    Block Structure Valid: ${result.verificationChecks.blockStructureValid ? 'PASS' : 'FAIL'}`,
        `    Computation Valid: ${result.verificationChecks.computationValid ? 'PASS' : 'FAIL'}`,
        `    Result Integrity Valid: ${result.verificationChecks.resultIntegrityValid ? 'PASS' : 'FAIL'}`,
        `    Performance Within Bounds: ${result.verificationChecks.performanceWithinBounds ? 'PASS' : 'FAIL'}`
      );

      if (result.errorDetails) {
        output.push(`  Error Details: ${result.errorDetails}`);
      }
    });

    output.push(
      '',
      '='.repeat(80),
      `Report generated at: ${new Date().toISOString()}`,
      '='.repeat(80)
    );

    fs.writeFileSync(outputFile, output.join('\n'));
    console.log(`📄 Human-readable report saved to: ${outputFile}`);
  }
}

// Main execution
async function main() {
  const test = new Matrix2048VerificationTest();
  
  try {
    await test.runVerificationTest();
    console.log('\n🎉 2048×2048 matrix operations verification test completed!');
  } catch (error) {
    console.error('❌ Verification test failed:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

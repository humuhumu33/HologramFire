/**
 * Real SDK Throughput Test
 * 
 * This test specifically measures throughput using the real SDK implementation
 * to compare performance against the mock implementation.
 */

import { createParallelProcessor } from './parallel/processor';
import { PerfTimer } from './testkit';

/**
 * Test configuration for real SDK throughput
 */
const REAL_SDK_CONFIG = {
  testDuration: 5, // 5 seconds per test
  concurrency: [1, 4, 8, 16],
  dataSizes: [1024, 10240, 102400], // 1KB, 10KB, 100KB
  operations: ['transport', 'storage', 'compute', 'postcards'],
};

/**
 * Test results structure
 */
interface RealSDKResult {
  operation: string;
  concurrency: number;
  dataSize: number;
  totalOperations: number;
  successfulOperations: number;
  totalTime: number;
  throughput: number; // operations per second
  dataThroughput: number; // bytes per second
  avgLatency: number;
  successRate: number;
}

/**
 * Generate test data
 */
function generateTestData(size: number): Buffer {
  const data = Buffer.alloc(size);
  for (let i = 0; i < size; i++) {
    data[i] = (i * 7 + (i % 256)) % 256;
  }
  return data;
}

/**
 * Test transport throughput with real SDK
 */
async function testRealSDKTransport(
  concurrency: number,
  dataSize: number,
  duration: number
): Promise<RealSDKResult> {
  console.log(`🚀 Testing Real SDK Transport: ${concurrency} concurrent, ${dataSize} bytes, ${duration}s`);
  
  const processor = createParallelProcessor({
    maxConcurrency: concurrency,
    timeout: 30000,
    retryAttempts: 3,
    retryDelay: 100,
  });
  
  await processor.initialize();
  
  const testData = generateTestData(dataSize);
  const operations = [];
  
  // Generate transport operations
  for (let i = 0; i < concurrency * 10; i++) {
    operations.push({
      lane: i % 8,
      payload: testData,
      budget: { io: 100, cpuMs: 50 },
      attach: { r96: `test-r96-${i}`, probes: 192 },
    });
  }
  
  const timer = new PerfTimer('Real SDK Transport');
  const results = await processor.parallelTransport(operations, {
    nodeId: 'real-sdk-test',
    lanes: 8,
    windowMs: 1000,
  });
  const totalTime = timer.end();
  
  await processor.cleanup();
  
  const successful = results.filter(r => r.success);
  const totalBytes = successful.length * dataSize;
  
  return {
    operation: 'transport',
    concurrency,
    dataSize,
    totalOperations: results.length,
    successfulOperations: successful.length,
    totalTime,
    throughput: successful.length / (totalTime / 1000),
    dataThroughput: totalBytes / (totalTime / 1000),
    avgLatency: successful.length > 0 ? successful.reduce((sum, r) => sum + r.duration, 0) / successful.length : 0,
    successRate: successful.length / results.length,
  };
}

/**
 * Test storage throughput with real SDK
 */
async function testRealSDKStorage(
  concurrency: number,
  dataSize: number,
  duration: number
): Promise<RealSDKResult> {
  console.log(`💾 Testing Real SDK Storage: ${concurrency} concurrent, ${dataSize} bytes, ${duration}s`);
  
  const processor = createParallelProcessor({
    maxConcurrency: concurrency,
    timeout: 30000,
    retryAttempts: 3,
    retryDelay: 100,
  });
  
  await processor.initialize();
  
  const testData = generateTestData(dataSize);
  const operations = [];
  
  // Generate storage operations
  for (let i = 0; i < concurrency * 10; i++) {
    operations.push({
      id: `real-sdk-storage-${i}`,
      bytes: testData,
      policy: { replication: 3 },
      budget: { io: 100, cpuMs: 50 },
      witness: {
        r96: `test-r96-${i}`,
        probes: 192,
        timestamp: Date.now(),
      },
    });
  }
  
  const timer = new PerfTimer('Real SDK Storage');
  const results = await processor.parallelStorage(operations, {
    rows: 48,
    cols: 256,
    tileCols: 8,
    ec: { k: 3, m: 2 },
  });
  const totalTime = timer.end();
  
  await processor.cleanup();
  
  const successful = results.filter(r => r.success);
  const totalBytes = successful.length * dataSize;
  
  return {
    operation: 'storage',
    concurrency,
    dataSize,
    totalOperations: results.length,
    successfulOperations: successful.length,
    totalTime,
    throughput: successful.length / (totalTime / 1000),
    dataThroughput: totalBytes / (totalTime / 1000),
    avgLatency: successful.length > 0 ? successful.reduce((sum, r) => sum + r.duration, 0) / successful.length : 0,
    successRate: successful.length / results.length,
  };
}

/**
 * Test compute throughput with real SDK
 */
async function testRealSDKCompute(
  concurrency: number,
  dataSize: number,
  duration: number
): Promise<RealSDKResult> {
  console.log(`⚙️  Testing Real SDK Compute: ${concurrency} concurrent, ${dataSize} bytes, ${duration}s`);
  
  const processor = createParallelProcessor({
    maxConcurrency: concurrency,
    timeout: 30000,
    retryAttempts: 3,
    retryDelay: 100,
  });
  
  await processor.initialize();
  
  const operations = [];
  
  // Generate compute operations
  for (let i = 0; i < concurrency * 5; i++) {
    operations.push({
      name: `real-sdk-compute-${i}`,
      inputs: [{ id: `input-${i}` }],
      budget: { io: 200, cpuMs: 100 },
      pin: { near: `input-${i}`, lane: i % 4 },
    });
  }
  
  const timer = new PerfTimer('Real SDK Compute');
  const results = await processor.parallelCompute(operations, {
    rows: 48,
    cols: 256,
    tileCols: 8,
    ec: { k: 3, m: 2 },
  });
  const totalTime = timer.end();
  
  await processor.cleanup();
  
  const successful = results.filter(r => r.success);
  const totalBytes = successful.length * dataSize;
  
  return {
    operation: 'compute',
    concurrency,
    dataSize,
    totalOperations: results.length,
    successfulOperations: successful.length,
    totalTime,
    throughput: successful.length / (totalTime / 1000),
    dataThroughput: totalBytes / (totalTime / 1000),
    avgLatency: successful.length > 0 ? successful.reduce((sum, r) => sum + r.duration, 0) / successful.length : 0,
    successRate: successful.length / results.length,
  };
}

/**
 * Test postcard throughput with real SDK
 */
async function testRealSDKPostcards(
  concurrency: number,
  dataSize: number,
  duration: number
): Promise<RealSDKResult> {
  console.log(`📮 Testing Real SDK Postcards: ${concurrency} concurrent, ${dataSize} bytes, ${duration}s`);
  
  const processor = createParallelProcessor({
    maxConcurrency: concurrency,
    timeout: 30000,
    retryAttempts: 3,
    retryDelay: 100,
  });
  
  await processor.initialize();
  
  const testData = generateTestData(dataSize);
  const postcards = [];
  
  // Generate postcards
  for (let i = 0; i < concurrency * 10; i++) {
    postcards.push({
      id: `real-sdk-postcard-${i}`,
      message: testData.toString('base64'),
      from: 'RealSDKTest',
      to: 'Target',
      timestamp: Date.now(),
      bytes: testData,
    });
  }
  
  const timer = new PerfTimer('Real SDK Postcards');
  const results = await processor.parallelPostcards(postcards, {
    rows: 48,
    cols: 256,
    tileCols: 8,
    ec: { k: 3, m: 2 },
  });
  const totalTime = timer.end();
  
  await processor.cleanup();
  
  const successful = results.filter(r => r.success);
  const totalBytes = successful.length * dataSize;
  
  return {
    operation: 'postcards',
    concurrency,
    dataSize,
    totalOperations: results.length,
    successfulOperations: successful.length,
    totalTime,
    throughput: successful.length / (totalTime / 1000),
    dataThroughput: totalBytes / (totalTime / 1000),
    avgLatency: successful.length > 0 ? successful.reduce((sum, r) => sum + r.duration, 0) / successful.length : 0,
    successRate: successful.length / results.length,
  };
}

/**
 * Format bytes to human readable format
 */
function formatBytes(bytes: number): string {
  const units = ['B', 'KB', 'MB', 'GB'];
  let size = bytes;
  let unitIndex = 0;
  
  while (size >= 1024 && unitIndex < units.length - 1) {
    size /= 1024;
    unitIndex++;
  }
  
  return `${size.toFixed(2)} ${units[unitIndex]}`;
}

/**
 * Format test result
 */
function formatResult(result: RealSDKResult): void {
  console.log(`\n📊 ${result.operation.toUpperCase()} Results:`);
  console.log(`   Concurrency: ${result.concurrency}`);
  console.log(`   Data Size: ${formatBytes(result.dataSize)}`);
  console.log(`   Total Operations: ${result.totalOperations}`);
  console.log(`   Successful: ${result.successfulOperations}`);
  console.log(`   Success Rate: ${(result.successRate * 100).toFixed(2)}%`);
  console.log(`   Throughput: ${result.throughput.toFixed(2)} ops/s`);
  console.log(`   Data Throughput: ${formatBytes(result.dataThroughput)}/s`);
  console.log(`   Avg Latency: ${result.avgLatency.toFixed(2)}ms`);
  console.log(`   Total Time: ${(result.totalTime / 1000).toFixed(2)}s`);
}

/**
 * Run real SDK throughput test
 */
export async function runRealSDKThroughputTest(): Promise<void> {
  console.log('\n🚀 REAL SDK THROUGHPUT TEST');
  console.log('='.repeat(60));
  console.log('🔧 Mode: REAL SDK');
  console.log(`⏱️  Test Duration: ${REAL_SDK_CONFIG.testDuration}s per test`);
  console.log(`📊 Concurrency Levels: ${REAL_SDK_CONFIG.concurrency.join(', ')}`);
  console.log(`📦 Data Sizes: ${REAL_SDK_CONFIG.dataSizes.map(formatBytes).join(', ')}`);
  console.log('='.repeat(60));
  
  const allResults: RealSDKResult[] = [];
  
  // Test each operation type
  const testFunctions = [
    { name: 'Transport', fn: testRealSDKTransport },
    { name: 'Storage', fn: testRealSDKStorage },
    { name: 'Compute', fn: testRealSDKCompute },
    { name: 'Postcards', fn: testRealSDKPostcards },
  ];
  
  for (const test of testFunctions) {
    console.log(`\n🔧 Testing ${test.name} Operations...`);
    console.log('─'.repeat(40));
    
    for (const concurrency of REAL_SDK_CONFIG.concurrency) {
      for (const dataSize of REAL_SDK_CONFIG.dataSizes) {
        try {
          const result = await test.fn(concurrency, dataSize, REAL_SDK_CONFIG.testDuration);
          allResults.push(result);
          formatResult(result);
        } catch (error) {
          console.error(`❌ Test failed for ${test.name}: ${error}`);
        }
      }
    }
  }
  
  // Generate summary
  console.log('\n📈 REAL SDK THROUGHPUT SUMMARY');
  console.log('='.repeat(60));
  
  const maxThroughput = Math.max(...allResults.map(r => r.throughput));
  const maxDataThroughput = Math.max(...allResults.map(r => r.dataThroughput));
  const bestResult = allResults.find(r => r.throughput === maxThroughput);
  const bestDataResult = allResults.find(r => r.dataThroughput === maxDataThroughput);
  
  console.log(`🏆 Best Operation Throughput: ${maxThroughput.toFixed(2)} ops/s`);
  console.log(`   Operation: ${bestResult?.operation}`);
  console.log(`   Concurrency: ${bestResult?.concurrency}`);
  console.log(`   Data Size: ${bestResult ? formatBytes(bestResult.dataSize) : 'N/A'}`);
  
  console.log(`\n🏆 Best Data Throughput: ${formatBytes(maxDataThroughput)}/s`);
  console.log(`   Operation: ${bestDataResult?.operation}`);
  console.log(`   Concurrency: ${bestDataResult?.concurrency}`);
  console.log(`   Data Size: ${bestDataResult ? formatBytes(bestDataResult.dataSize) : 'N/A'}`);
  
  // Performance by operation
  console.log('\n📊 Performance by Operation:');
  const byOperation = allResults.reduce((acc, result) => {
    if (!acc[result.operation]) {
      acc[result.operation] = [];
    }
    acc[result.operation]!.push(result.throughput);
    return acc;
  }, {} as Record<string, number[]>);
  
  for (const [operation, throughputs] of Object.entries(byOperation)) {
    const max = Math.max(...throughputs);
    const avg = throughputs.reduce((a, b) => a + b, 0) / throughputs.length;
    console.log(`   ${operation}: Max ${max.toFixed(2)} ops/s, Avg ${avg.toFixed(2)} ops/s`);
  }
  
  console.log(`\n📋 Test completed with ${allResults.length} individual test runs`);
  console.log('🎯 Real SDK implementation successfully tested!');
}

/**
 * Main function
 */
async function main(): Promise<void> {
  try {
    await runRealSDKThroughputTest();
    console.log('\n🎉 Real SDK throughput test completed successfully!');
  } catch (error) {
    console.error('\n❌ Real SDK throughput test failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

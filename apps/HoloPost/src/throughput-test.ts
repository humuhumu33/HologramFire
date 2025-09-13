/**
 * HoloPost Throughput Capacity Test
 * 
 * This test measures the actual throughput capacity of HoloPost and compares
 * it to the original Hologram implementation's promised 25 GB/s.
 * 
 * The test measures:
 * - Data processing throughput (bytes/second)
 * - Operations per second (ops/sec)
 * - End-to-end latency
 * - Memory usage patterns
 * - Network simulation capacity
 */

import { createVerifier, createCTP, createStorage, spawnKernel } from './adapters/hologram';
import { createPostcardWitness } from './usecases/postcard';
import { mkBudget } from './testkit';
import { Buffer } from 'node:buffer';

/**
 * Test configuration for throughput measurement
 */
const THROUGHPUT_CONFIG = {
  // Data sizes to test (in bytes)
  dataSizes: [
    1024,        // 1 KB
    10240,       // 10 KB
    102400,      // 100 KB
    1048576,     // 1 MB
    10485760,    // 10 MB
    104857600,   // 100 MB
  ],
  
  // Test durations (in seconds)
  testDuration: 10,
  
  // Concurrent operations
  concurrency: [1, 5, 10, 25, 50, 100],
  
  // Target throughput (original promise)
  targetThroughput: 25 * 1024 * 1024 * 1024, // 25 GB/s
  
  // Lattice configuration
  lattice: {
    rows: 48,
    cols: 256,
    totalCells: 12288,
  },
};

/**
 * Test results structure
 */
interface ThroughputResult {
  operation: string;
  dataSize: number;
  concurrency: number;
  totalBytes: number;
  totalTime: number;
  throughput: number; // bytes/second
  opsPerSecond: number;
  avgLatency: number; // milliseconds
  successRate: number;
  memoryUsage?: {
    peak: number;
    average: number;
  };
}

/**
 * Memory usage tracker
 */
class MemoryTracker {
  private samples: number[] = [];
  private peak = 0;

  start(): void {
    this.samples = [];
    this.peak = 0;
  }

  sample(): void {
    const usage = process.memoryUsage();
    const total = usage.heapUsed + usage.external;
    this.samples.push(total);
    this.peak = Math.max(this.peak, total);
  }

  getResults(): { peak: number; average: number } {
    const average = this.samples.length > 0 
      ? this.samples.reduce((a, b) => a + b, 0) / this.samples.length 
      : 0;
    return {
      peak: this.peak,
      average: average,
    };
  }
}

/**
 * Generate test data of specified size
 */
function generateTestData(size: number): Buffer {
  const data = Buffer.alloc(size);
  // Fill with deterministic but varied data
  for (let i = 0; i < size; i++) {
    data[i] = (i * 7 + (i % 256)) % 256;
  }
  return data;
}

/**
 * Test transport throughput
 */
async function testTransportThroughput(
  dataSize: number, 
  concurrency: number, 
  duration: number
): Promise<ThroughputResult> {
  console.log(`🚀 Testing Transport Throughput: ${dataSize} bytes, ${concurrency} concurrent, ${duration}s`);
  
  const memoryTracker = new MemoryTracker();
  memoryTracker.start();
  
  const testData = generateTestData(dataSize);
  const results: Array<{ bytes: number; time: number; success: boolean }> = [];
  
  const startTime = Date.now();
  const endTime = startTime + (duration * 1000);
  
  // Create CTP instances for concurrent operations
  const ctpInstances = await Promise.all(
    Array(concurrency).fill(0).map(() => createCTP({
      nodeId: `throughput-test-${Math.random()}`,
      lanes: 8,
      windowMs: 100,
    }))
  );
  
  const verifier = await createVerifier();
  const budget = mkBudget(10000, 1000, 100);
  
  // Run concurrent operations
  const operations = ctpInstances.map(async (ctp, index) => {
    let operationCount = 0;
    
    while (Date.now() < endTime) {
      try {
        const opStart = Date.now();
        
        // Create postcard with test data
        const postcard = {
          id: `test-${index}-${operationCount}`,
          message: testData.toString('base64'),
          from: 'ThroughputTest',
          to: 'Target',
          timestamp: Date.now(),
          bytes: testData,
        };
        
        const witness = await createPostcardWitness(postcard);
        
        // Perform handshake
        await ctp.handshake({
          nodeId: `test-${index}`,
          capabilities: ['transport'],
        });
        
        // Send data
        await ctp.send({
          lane: index % 8,
          payload: testData,
          budget,
          attach: {
            r96: witness.r96,
            probes: witness.probes,
          },
        });
        
        // Receive data (simulated)
        const recvResult = await ctp.recv();
        
        // Verify
        const kleinValid = verifier.klein(recvResult.frame);
        const r96Valid = verifier.r96(recvResult.payload) === witness.r96;
        
        // Settle
        await ctp.settle(recvResult.windowId);
        
        const opTime = Date.now() - opStart;
        
        results.push({
          bytes: dataSize,
          time: opTime,
          success: kleinValid && r96Valid,
        });
        
        operationCount++;
        memoryTracker.sample();
        
      } catch (error) {
        results.push({
          bytes: dataSize,
          time: 0,
          success: false,
        });
      }
    }
  });
  
  await Promise.all(operations);
  
  // Clean up
  await Promise.all(ctpInstances.map(ctp => ctp.close()));
  
  const totalTime = Date.now() - startTime;
  const successfulOps = results.filter(r => r.success);
  const totalBytes = successfulOps.reduce((sum, r) => sum + r.bytes, 0);
  const avgLatency = successfulOps.length > 0 
    ? successfulOps.reduce((sum, r) => sum + r.time, 0) / successfulOps.length 
    : 0;
  
  return {
    operation: 'transport',
    dataSize,
    concurrency,
    totalBytes,
    totalTime,
    throughput: totalBytes / (totalTime / 1000),
    opsPerSecond: successfulOps.length / (totalTime / 1000),
    avgLatency,
    successRate: successfulOps.length / results.length,
    memoryUsage: memoryTracker.getResults(),
  };
}

/**
 * Test storage throughput
 */
async function testStorageThroughput(
  dataSize: number, 
  concurrency: number, 
  duration: number
): Promise<ThroughputResult> {
  console.log(`💾 Testing Storage Throughput: ${dataSize} bytes, ${concurrency} concurrent, ${duration}s`);
  
  const memoryTracker = new MemoryTracker();
  memoryTracker.start();
  
  const testData = generateTestData(dataSize);
  const results: Array<{ bytes: number; time: number; success: boolean }> = [];
  
  const startTime = Date.now();
  const endTime = startTime + (duration * 1000);
  
  // Create storage instances for concurrent operations
  const storageInstances = await Promise.all(
    Array(concurrency).fill(0).map(() => createStorage({
      rows: THROUGHPUT_CONFIG.lattice.rows,
      cols: THROUGHPUT_CONFIG.lattice.cols,
      tileCols: 16,
      ec: { k: 3, m: 2 },
    }))
  );
  
  const budget = mkBudget(10000, 1000, 100);
  
  // Run concurrent operations
  const operations = storageInstances.map(async (storage, index) => {
    let operationCount = 0;
    
    while (Date.now() < endTime) {
      try {
        const opStart = Date.now();
        
        const id = `storage-test-${index}-${operationCount}`;
        const witness = await createPostcardWitness({
          id,
          message: testData.toString('base64'),
          from: 'StorageTest',
          to: 'Target',
          timestamp: Date.now(),
          bytes: testData,
        });
        
        // Store data
        const putReceipt = await storage.put({
          id,
          bytes: testData,
          policy: {
            replication: 3,
            erasureCoding: { k: 3, m: 2 },
            placement: [],
          },
          budget,
          witness,
        });
        
        // Retrieve data
        const getResult = await storage.get({
          id,
          policy: { verifyWitness: true },
        });
        
        const opTime = Date.now() - opStart;
        
        results.push({
          bytes: dataSize,
          time: opTime,
          success: putReceipt.ok && getResult.bytes.length === dataSize,
        });
        
        operationCount++;
        memoryTracker.sample();
        
      } catch (error) {
        results.push({
          bytes: dataSize,
          time: 0,
          success: false,
        });
      }
    }
  });
  
  await Promise.all(operations);
  
  const totalTime = Date.now() - startTime;
  const successfulOps = results.filter(r => r.success);
  const totalBytes = successfulOps.reduce((sum, r) => sum + r.bytes, 0);
  const avgLatency = successfulOps.length > 0 
    ? successfulOps.reduce((sum, r) => sum + r.time, 0) / successfulOps.length 
    : 0;
  
  return {
    operation: 'storage',
    dataSize,
    concurrency,
    totalBytes,
    totalTime,
    throughput: totalBytes / (totalTime / 1000),
    opsPerSecond: successfulOps.length / (totalTime / 1000),
    avgLatency,
    successRate: successfulOps.length / results.length,
    memoryUsage: memoryTracker.getResults(),
  };
}

/**
 * Test compute throughput
 */
async function testComputeThroughput(
  dataSize: number, 
  concurrency: number, 
  duration: number
): Promise<ThroughputResult> {
  console.log(`⚡ Testing Compute Throughput: ${dataSize} bytes, ${concurrency} concurrent, ${duration}s`);
  
  const memoryTracker = new MemoryTracker();
  memoryTracker.start();
  
  const testData = generateTestData(dataSize);
  const results: Array<{ bytes: number; time: number; success: boolean }> = [];
  
  const startTime = Date.now();
  const endTime = startTime + (duration * 1000);
  
  // Create storage for input data
  const storage = await createStorage({
    rows: THROUGHPUT_CONFIG.lattice.rows,
    cols: THROUGHPUT_CONFIG.lattice.cols,
    tileCols: 16,
    ec: { k: 3, m: 2 },
  });
  
  const budget = mkBudget(10000, 1000, 100);
  
  // Run concurrent operations
  const operations = Array(concurrency).fill(0).map(async (_, index) => {
    let operationCount = 0;
    
    while (Date.now() < endTime) {
      try {
        const opStart = Date.now();
        
        const id = `compute-test-${index}-${operationCount}`;
        const witness = await createPostcardWitness({
          id,
          message: testData.toString('base64'),
          from: 'ComputeTest',
          to: 'Target',
          timestamp: Date.now(),
          bytes: testData,
        });
        
        // Store input data
        await storage.put({
          id,
          bytes: testData,
          policy: {},
          budget,
          witness,
        });
        
        // Spawn kernel
        const kernel = await spawnKernel({
          name: 'throughput-test-kernel',
          inputs: [{ id }],
          budget,
        });
        
        // Execute kernel
        const result = await kernel.await();
        
        const opTime = Date.now() - opStart;
        
        results.push({
          bytes: dataSize,
          time: opTime,
          success: result.ok && result.outputs.length > 0,
        });
        
        operationCount++;
        memoryTracker.sample();
        
      } catch (error) {
        results.push({
          bytes: dataSize,
          time: 0,
          success: false,
        });
      }
    }
  });
  
  await Promise.all(operations);
  
  const totalTime = Date.now() - startTime;
  const successfulOps = results.filter(r => r.success);
  const totalBytes = successfulOps.reduce((sum, r) => sum + r.bytes, 0);
  const avgLatency = successfulOps.length > 0 
    ? successfulOps.reduce((sum, r) => sum + r.time, 0) / successfulOps.length 
    : 0;
  
  return {
    operation: 'compute',
    dataSize,
    concurrency,
    totalBytes,
    totalTime,
    throughput: totalBytes / (totalTime / 1000),
    opsPerSecond: successfulOps.length / (totalTime / 1000),
    avgLatency,
    successRate: successfulOps.length / results.length,
    memoryUsage: memoryTracker.getResults(),
  };
}

/**
 * Format bytes to human readable format
 */
function formatBytes(bytes: number): string {
  const units = ['B', 'KB', 'MB', 'GB', 'TB'];
  let size = bytes;
  let unitIndex = 0;
  
  while (size >= 1024 && unitIndex < units.length - 1) {
    size /= 1024;
    unitIndex++;
  }
  
  return `${size.toFixed(2)} ${units[unitIndex]}`;
}

/**
 * Format throughput results
 */
function formatThroughputResult(result: ThroughputResult): void {
  console.log(`\n📊 ${result.operation.toUpperCase()} Throughput Results:`);
  console.log(`   Data Size: ${formatBytes(result.dataSize)}`);
  console.log(`   Concurrency: ${result.concurrency}`);
  console.log(`   Total Bytes: ${formatBytes(result.totalBytes)}`);
  console.log(`   Total Time: ${(result.totalTime / 1000).toFixed(2)}s`);
  console.log(`   Throughput: ${formatBytes(result.throughput)}/s`);
  console.log(`   Operations/sec: ${result.opsPerSecond.toFixed(2)}`);
  console.log(`   Avg Latency: ${result.avgLatency.toFixed(2)}ms`);
  console.log(`   Success Rate: ${(result.successRate * 100).toFixed(2)}%`);
  
  if (result.memoryUsage) {
    console.log(`   Peak Memory: ${formatBytes(result.memoryUsage.peak)}`);
    console.log(`   Avg Memory: ${formatBytes(result.memoryUsage.average)}`);
  }
  
  // Compare to target
  const targetRatio = result.throughput / THROUGHPUT_CONFIG.targetThroughput;
  console.log(`   vs Target (25 GB/s): ${(targetRatio * 100).toFixed(4)}%`);
}

/**
 * Run comprehensive throughput test
 */
export async function runThroughputTest(): Promise<void> {
  console.log('\n🚀 HOLOPOST THROUGHPUT CAPACITY TEST');
  console.log('='.repeat(60));
  console.log(`🎯 Target: ${formatBytes(THROUGHPUT_CONFIG.targetThroughput)}/s (Original Hologram Promise)`);
  console.log(`🏗️  Lattice: ${THROUGHPUT_CONFIG.lattice.rows}×${THROUGHPUT_CONFIG.lattice.cols} = ${THROUGHPUT_CONFIG.lattice.totalCells} cells`);
  console.log(`⏱️  Test Duration: ${THROUGHPUT_CONFIG.testDuration}s per test`);
  console.log('='.repeat(60));
  
  const allResults: ThroughputResult[] = [];
  
  // Test each operation type
  const operations = [
    { name: 'Transport', fn: testTransportThroughput },
    { name: 'Storage', fn: testStorageThroughput },
    { name: 'Compute', fn: testComputeThroughput },
  ];
  
  for (const op of operations) {
    console.log(`\n🔧 Testing ${op.name} Operations...`);
    console.log('─'.repeat(40));
    
    // Test different data sizes and concurrency levels
    for (const dataSize of THROUGHPUT_CONFIG.dataSizes) {
      for (const concurrency of THROUGHPUT_CONFIG.concurrency) {
        try {
          const result = await op.fn(dataSize, concurrency, THROUGHPUT_CONFIG.testDuration);
          allResults.push(result);
          formatThroughputResult(result);
        } catch (error) {
          console.error(`❌ Test failed for ${op.name}: ${error}`);
        }
      }
    }
  }
  
  // Generate summary report
  console.log('\n📈 THROUGHPUT TEST SUMMARY');
  console.log('='.repeat(60));
  
  const maxThroughput = Math.max(...allResults.map(r => r.throughput));
  const bestResult = allResults.find(r => r.throughput === maxThroughput);
  
  console.log(`🏆 Best Throughput: ${formatBytes(maxThroughput)}/s`);
  console.log(`   Operation: ${bestResult?.operation}`);
  console.log(`   Data Size: ${bestResult ? formatBytes(bestResult.dataSize) : 'N/A'}`);
  console.log(`   Concurrency: ${bestResult?.concurrency}`);
  console.log(`   vs Target: ${((maxThroughput / THROUGHPUT_CONFIG.targetThroughput) * 100).toFixed(4)}%`);
  
  // Performance by operation type
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
    console.log(`   ${operation}: Max ${formatBytes(max)}/s, Avg ${formatBytes(avg)}/s`);
  }
  
  // Performance by data size
  console.log('\n📊 Performance by Data Size:');
  const byDataSize = allResults.reduce((acc, result) => {
    if (!acc[result.dataSize]) {
      acc[result.dataSize] = [];
    }
    acc[result.dataSize]!.push(result.throughput);
    return acc;
  }, {} as Record<number, number[]>);
  
  for (const [dataSize, throughputs] of Object.entries(byDataSize)) {
    const max = Math.max(...throughputs);
    const avg = throughputs.reduce((a, b) => a + b, 0) / throughputs.length;
    console.log(`   ${formatBytes(Number(dataSize))}: Max ${formatBytes(max)}/s, Avg ${formatBytes(avg)}/s`);
  }
  
  // Final assessment
  console.log('\n🎯 FINAL ASSESSMENT');
  console.log('='.repeat(60));
  
  if (maxThroughput >= THROUGHPUT_CONFIG.targetThroughput) {
    console.log('✅ HoloPost MEETS the original 25 GB/s promise!');
  } else {
    const gap = THROUGHPUT_CONFIG.targetThroughput - maxThroughput;
    const gapPercent = (gap / THROUGHPUT_CONFIG.targetThroughput) * 100;
    console.log(`❌ HoloPost is ${formatBytes(gap)}/s (${gapPercent.toFixed(2)}%) below the 25 GB/s promise`);
  }
  
  console.log(`\n📋 Test completed with ${allResults.length} individual test runs`);
  console.log(`🔧 Mode: ${process.env['HOLOGRAM_USE_MOCK'] !== 'false' ? 'MOCK' : 'REAL SDK'}`);
}

/**
 * Main function for running throughput test standalone
 */
async function main(): Promise<void> {
  const args = process.argv.slice(2);
  
  // Check for --real flag
  if (args.includes('--real')) {
    process.env['HOLOGRAM_USE_MOCK'] = 'false';
    console.log('🚀 Using REAL SDK implementation for throughput test');
  } else {
    console.log('🔧 Using MOCK SDK implementation for throughput test');
  }
  
  try {
    await runThroughputTest();
    console.log('\n🎉 Throughput test completed successfully!');
  } catch (error) {
    console.error('\n❌ Throughput test failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

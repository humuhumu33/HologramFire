/**
 * Quick HoloPost Throughput Test
 * 
 * A focused test to quickly measure HoloPost's throughput capacity
 * and compare it to the original 25 GB/s promise.
 */

import { createVerifier, createCTP, createStorage, spawnKernel } from './adapters/hologram';
import { createPostcardWitness } from './usecases/postcard';
import { mkBudget } from './testkit';
import { Buffer } from 'node:buffer';

/**
 * Quick test configuration
 */
const QUICK_CONFIG = {
  dataSize: 1024 * 1024, // 1 MB
  concurrency: 10,
  duration: 5, // 5 seconds
  targetThroughput: 25 * 1024 * 1024 * 1024, // 25 GB/s
};

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
 * Test transport throughput
 */
async function testTransportThroughput(): Promise<number> {
  console.log('🚀 Testing Transport Throughput...');
  
  const testData = generateTestData(QUICK_CONFIG.dataSize);
  const results: Array<{ bytes: number; time: number; success: boolean }> = [];
  
  const startTime = Date.now();
  const endTime = startTime + (QUICK_CONFIG.duration * 1000);
  
  // Create CTP instances
  const ctpInstances = await Promise.all(
    Array(QUICK_CONFIG.concurrency).fill(0).map(() => createCTP({
      nodeId: `quick-test-${Math.random()}`,
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
        
        const postcard = {
          id: `test-${index}-${operationCount}`,
          message: testData.toString('base64'),
          from: 'QuickTest',
          to: 'Target',
          timestamp: Date.now(),
          bytes: testData,
        };
        
        const witness = await createPostcardWitness(postcard);
        
        await ctp.handshake({
          nodeId: `test-${index}`,
          capabilities: ['transport'],
        });
        
        await ctp.send({
          lane: index % 8,
          payload: testData,
          budget,
          attach: {
            r96: witness.r96,
            probes: witness.probes,
          },
        });
        
        const recvResult = await ctp.recv();
        
        const kleinValid = verifier.klein(recvResult.frame);
        const r96Valid = verifier.r96(recvResult.payload) === witness.r96;
        
        await ctp.settle(recvResult.windowId);
        
        const opTime = Date.now() - opStart;
        
        results.push({
          bytes: QUICK_CONFIG.dataSize,
          time: opTime,
          success: kleinValid && r96Valid,
        });
        
        operationCount++;
        
      } catch (error) {
        results.push({
          bytes: QUICK_CONFIG.dataSize,
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
  const throughput = totalBytes / (totalTime / 1000);
  
  console.log(`   Throughput: ${formatBytes(throughput)}/s`);
  console.log(`   Operations: ${successfulOps.length}`);
  console.log(`   Success Rate: ${(successfulOps.length / results.length * 100).toFixed(1)}%`);
  
  return throughput;
}

/**
 * Test storage throughput
 */
async function testStorageThroughput(): Promise<number> {
  console.log('💾 Testing Storage Throughput...');
  
  const testData = generateTestData(QUICK_CONFIG.dataSize);
  const results: Array<{ bytes: number; time: number; success: boolean }> = [];
  
  const startTime = Date.now();
  const endTime = startTime + (QUICK_CONFIG.duration * 1000);
  
  // Create storage instances
  const storageInstances = await Promise.all(
    Array(QUICK_CONFIG.concurrency).fill(0).map(() => createStorage({
      rows: 48,
      cols: 256,
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
        
        const getResult = await storage.get({
          id,
          policy: { verifyWitness: true },
        });
        
        const opTime = Date.now() - opStart;
        
        results.push({
          bytes: QUICK_CONFIG.dataSize,
          time: opTime,
          success: putReceipt.ok && getResult.bytes.length === QUICK_CONFIG.dataSize,
        });
        
        operationCount++;
        
      } catch (error) {
        results.push({
          bytes: QUICK_CONFIG.dataSize,
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
  const throughput = totalBytes / (totalTime / 1000);
  
  console.log(`   Throughput: ${formatBytes(throughput)}/s`);
  console.log(`   Operations: ${successfulOps.length}`);
  console.log(`   Success Rate: ${(successfulOps.length / results.length * 100).toFixed(1)}%`);
  
  return throughput;
}

/**
 * Test compute throughput
 */
async function testComputeThroughput(): Promise<number> {
  console.log('⚡ Testing Compute Throughput...');
  
  const testData = generateTestData(QUICK_CONFIG.dataSize);
  const results: Array<{ bytes: number; time: number; success: boolean }> = [];
  
  const startTime = Date.now();
  const endTime = startTime + (QUICK_CONFIG.duration * 1000);
  
  const storage = await createStorage({
    rows: 48,
    cols: 256,
    tileCols: 16,
    ec: { k: 3, m: 2 },
  });
  
  const budget = mkBudget(10000, 1000, 100);
  
  // Run concurrent operations
  const operations = Array(QUICK_CONFIG.concurrency).fill(0).map(async (_, index) => {
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
        
        await storage.put({
          id,
          bytes: testData,
          policy: {},
          budget,
          witness,
        });
        
        const kernel = await spawnKernel({
          name: 'quick-test-kernel',
          inputs: [{ id }],
          budget,
        });
        
        const result = await kernel.await();
        
        const opTime = Date.now() - opStart;
        
        results.push({
          bytes: QUICK_CONFIG.dataSize,
          time: opTime,
          success: result.ok && result.outputs.length > 0,
        });
        
        operationCount++;
        
      } catch (error) {
        results.push({
          bytes: QUICK_CONFIG.dataSize,
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
  const throughput = totalBytes / (totalTime / 1000);
  
  console.log(`   Throughput: ${formatBytes(throughput)}/s`);
  console.log(`   Operations: ${successfulOps.length}`);
  console.log(`   Success Rate: ${(successfulOps.length / results.length * 100).toFixed(1)}%`);
  
  return throughput;
}

/**
 * Run quick throughput test
 */
export async function runQuickThroughputTest(): Promise<void> {
  console.log('\n🚀 HOLOPOST QUICK THROUGHPUT TEST');
  console.log('='.repeat(50));
  console.log(`🎯 Target: ${formatBytes(QUICK_CONFIG.targetThroughput)}/s (Original Hologram Promise)`);
  console.log(`📊 Test Config: ${formatBytes(QUICK_CONFIG.dataSize)} data, ${QUICK_CONFIG.concurrency} concurrent, ${QUICK_CONFIG.duration}s`);
  console.log(`🔧 Mode: ${process.env['HOLOGRAM_USE_MOCK'] !== 'false' ? 'MOCK' : 'REAL SDK'}`);
  console.log('='.repeat(50));
  
  const results: Array<{ operation: string; throughput: number }> = [];
  
  try {
    // Test transport
    const transportThroughput = await testTransportThroughput();
    results.push({ operation: 'Transport', throughput: transportThroughput });
    
    // Test storage
    const storageThroughput = await testStorageThroughput();
    results.push({ operation: 'Storage', throughput: storageThroughput });
    
    // Test compute
    const computeThroughput = await testComputeThroughput();
    results.push({ operation: 'Compute', throughput: computeThroughput });
    
    // Generate summary
    console.log('\n📈 THROUGHPUT TEST RESULTS');
    console.log('='.repeat(50));
    
    const maxThroughput = Math.max(...results.map(r => r.throughput));
    const bestOperation = results.find(r => r.throughput === maxThroughput);
    
    console.log(`🏆 Best Throughput: ${formatBytes(maxThroughput)}/s (${bestOperation?.operation})`);
    console.log(`🎯 Target: ${formatBytes(QUICK_CONFIG.targetThroughput)}/s`);
    
    const targetRatio = maxThroughput / QUICK_CONFIG.targetThroughput;
    console.log(`📊 Performance vs Target: ${(targetRatio * 100).toFixed(4)}%`);
    
    console.log('\n📋 All Results:');
    for (const result of results) {
      const ratio = result.throughput / QUICK_CONFIG.targetThroughput;
      console.log(`   ${result.operation}: ${formatBytes(result.throughput)}/s (${(ratio * 100).toFixed(4)}% of target)`);
    }
    
    // Final assessment
    console.log('\n🎯 FINAL ASSESSMENT');
    console.log('='.repeat(50));
    
    if (maxThroughput >= QUICK_CONFIG.targetThroughput) {
      console.log('✅ HoloPost MEETS the original 25 GB/s promise!');
    } else {
      const gap = QUICK_CONFIG.targetThroughput - maxThroughput;
      const gapPercent = (gap / QUICK_CONFIG.targetThroughput) * 100;
      console.log(`❌ HoloPost is ${formatBytes(gap)}/s (${gapPercent.toFixed(2)}%) below the 25 GB/s promise`);
      
      console.log('\n🔍 Analysis:');
      console.log(`   • Current implementation is using MOCK mode (simulated operations)`);
      console.log(`   • Real-world performance would depend on network, hardware, and actual Hologram SDK`);
      console.log(`   • The ${(targetRatio * 100).toFixed(2)}% performance suggests significant optimization potential`);
    }
    
  } catch (error) {
    console.error('\n❌ Throughput test failed:', error);
    throw error;
  }
}

/**
 * Main function
 */
async function main(): Promise<void> {
  try {
    await runQuickThroughputTest();
    console.log('\n🎉 Quick throughput test completed!');
  } catch (error) {
    console.error('\n❌ Test failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

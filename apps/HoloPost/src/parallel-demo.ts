/**
 * Parallel Processing Demo
 * 
 * This demo showcases the parallel processing capabilities of HoloPost,
 * demonstrating concurrent transport, storage, and compute operations.
 */

import { createParallelProcessor, ParallelConfig } from './parallel/processor';
import { Budget, Witness, Postcard } from './types';
import { PerfTimer } from './testkit';

/**
 * Demo configuration
 */
const DEMO_CONFIG = {
  title: 'HoloPost Parallel Processing Demo',
  subtitle: 'Concurrent Transport, Storage, and Compute Operations',
  version: '1.0.0',
};

/**
 * Parallel processing configuration
 */
const PARALLEL_CONFIG: ParallelConfig = {
  maxConcurrency: 4,
  timeout: 30000,
  retryAttempts: 3,
  retryDelay: 1000,
};

/**
 * Lattice configuration
 */
const LATTICE_CONFIG = {
  rows: 48,
  cols: 256,
  tileCols: 8,
  ec: { k: 3, m: 2 },
};

/**
 * CTP configuration
 */
const CTP_CONFIG = {
  nodeId: 'demo-node-001',
  lanes: 8,
  windowMs: 5000,
};

/**
 * Print demo banner
 */
function printBanner(): void {
  console.log('\n' + '='.repeat(80));
  console.log(`🚀 ${DEMO_CONFIG.title}`);
  console.log(`⚡ ${DEMO_CONFIG.subtitle}`);
  console.log(`📦 Version ${DEMO_CONFIG.version}`);
  console.log('='.repeat(80));
  console.log(`🔧 Mode: ${process.env['HOLOGRAM_USE_MOCK'] !== 'false' ? 'MOCK' : 'REAL SDK'}`);
  console.log(`⚡ Max Concurrency: ${PARALLEL_CONFIG.maxConcurrency}`);
  console.log(`⏱️  Timeout: ${PARALLEL_CONFIG.timeout}ms`);
  console.log(`🔄 Retry Attempts: ${PARALLEL_CONFIG.retryAttempts}`);
  console.log('='.repeat(80));
}

/**
 * Generate test data for parallel operations
 */
function generateTestData(): {
  postcards: Postcard[];
  transportOps: Array<{
    lane: number;
    payload: Buffer;
    budget: Budget;
    attach: { r96: string; probes: number };
  }>;
  storageOps: Array<{
    id: string;
    bytes: Buffer;
    policy: any;
    budget: Budget;
    witness: Witness;
  }>;
  computeOps: Array<{
    name: string;
    inputs: Array<{ id: string }>;
    budget: Budget;
    pin?: { near?: string; lane?: number };
  }>;
} {
  const postcards: Postcard[] = [];
  const transportOps: Array<{
    lane: number;
    payload: Buffer;
    budget: Budget;
    attach: { r96: string; probes: number };
  }> = [];
  const storageOps: Array<{
    id: string;
    bytes: Buffer;
    policy: any;
    budget: Budget;
    witness: Witness;
  }> = [];
  const computeOps: Array<{
    name: string;
    inputs: Array<{ id: string }>;
    budget: Budget;
    pin?: { near?: string; lane?: number };
  }> = [];

  // Generate test postcards
  for (let i = 0; i < 10; i++) {
    const message = `Parallel test message ${i + 1} - ${new Date().toISOString()}`;
    const postcard: Postcard = {
      id: `postcard-${i + 1}`,
      message,
      from: `sender-${i + 1}`,
      to: `recipient-${i + 1}`,
      timestamp: Date.now(),
      bytes: Buffer.from(JSON.stringify({
        id: `postcard-${i + 1}`,
        message,
        from: `sender-${i + 1}`,
        to: `recipient-${i + 1}`,
        timestamp: Date.now(),
      }), 'utf8'),
    };
    postcards.push(postcard);
  }

  // Generate transport operations
  for (let i = 0; i < 8; i++) {
    const payload = Buffer.from(`Transport payload ${i + 1}`, 'utf8');
    transportOps.push({
      lane: i % 4, // Distribute across 4 lanes
      payload,
      budget: { io: 50, cpuMs: 25 },
      attach: { r96: 'mock-r96-' + (i + 1), probes: 192 },
    });
  }

  // Generate storage operations
  for (let i = 0; i < 12; i++) {
    const content = `Storage content ${i + 1} - ${new Date().toISOString()}`;
    const bytes = Buffer.from(content, 'utf8');
    storageOps.push({
      id: `storage-${i + 1}`,
      bytes,
      policy: { replication: 3 },
      budget: { io: 100, cpuMs: 50 },
      witness: {
        r96: 'mock-r96-' + (i + 1),
        probes: 192,
        timestamp: Date.now(),
      },
    });
  }

  // Generate compute operations
  for (let i = 0; i < 6; i++) {
    computeOps.push({
      name: `compute-kernel-${i + 1}`,
      inputs: [
        { id: `storage-${i + 1}` },
        { id: `storage-${i + 2}` },
      ],
      budget: { io: 200, cpuMs: 100 },
      pin: { near: `storage-${i + 1}`, lane: i % 4 },
    });
  }

  return { postcards, transportOps, storageOps, computeOps };
}

/**
 * Run parallel transport demo
 */
async function runParallelTransportDemo(processor: any): Promise<void> {
  console.log('\n' + '─'.repeat(60));
  console.log('🚀 PARALLEL TRANSPORT DEMO');
  console.log('─'.repeat(60));

  const { transportOps } = generateTestData();
  const timer = new PerfTimer('Parallel Transport');

  try {
    const results = await processor.parallelTransport(transportOps, CTP_CONFIG);
    const stats = processor.getStats(results);

    console.log('\n📊 TRANSPORT RESULTS:');
    console.log(`   Total operations: ${stats.total}`);
    console.log(`   Successful: ${stats.successful}`);
    console.log(`   Failed: ${stats.failed}`);
    console.log(`   Average duration: ${stats.averageDuration.toFixed(2)}ms`);
    console.log(`   Total duration: ${stats.totalDuration}ms`);
    console.log(`   Total retries: ${stats.totalRetries}`);

    if (stats.failed > 0) {
      console.log('\n❌ FAILED OPERATIONS:');
      results.filter((r: any) => !r.success).forEach((result: any, i: number) => {
        console.log(`   ${i + 1}. ${result.error?.message}`);
      });
    }

    console.log(`\n✅ Parallel transport completed in ${timer.end()}ms`);
  } catch (error) {
    console.error('\n❌ Parallel transport failed:', error);
    throw error;
  }
}

/**
 * Run parallel storage demo
 */
async function runParallelStorageDemo(processor: any): Promise<void> {
  console.log('\n' + '─'.repeat(60));
  console.log('💾 PARALLEL STORAGE DEMO');
  console.log('─'.repeat(60));

  const { storageOps } = generateTestData();
  const timer = new PerfTimer('Parallel Storage');

  try {
    const results = await processor.parallelStorage(storageOps, LATTICE_CONFIG);
    const stats = processor.getStats(results);

    console.log('\n📊 STORAGE RESULTS:');
    console.log(`   Total operations: ${stats.total}`);
    console.log(`   Successful: ${stats.successful}`);
    console.log(`   Failed: ${stats.failed}`);
    console.log(`   Average duration: ${stats.averageDuration.toFixed(2)}ms`);
    console.log(`   Total duration: ${stats.totalDuration}ms`);
    console.log(`   Total retries: ${stats.totalRetries}`);

    if (stats.failed > 0) {
      console.log('\n❌ FAILED OPERATIONS:');
      results.filter((r: any) => !r.success).forEach((result: any, i: number) => {
        console.log(`   ${i + 1}. ${result.error?.message}`);
      });
    }

    console.log(`\n✅ Parallel storage completed in ${timer.end()}ms`);
  } catch (error) {
    console.error('\n❌ Parallel storage failed:', error);
    throw error;
  }
}

/**
 * Run parallel compute demo
 */
async function runParallelComputeDemo(processor: any): Promise<void> {
  console.log('\n' + '─'.repeat(60));
  console.log('⚙️  PARALLEL COMPUTE DEMO');
  console.log('─'.repeat(60));

  const { computeOps } = generateTestData();
  const timer = new PerfTimer('Parallel Compute');

  try {
    const results = await processor.parallelCompute(computeOps, LATTICE_CONFIG);
    const stats = processor.getStats(results);

    console.log('\n📊 COMPUTE RESULTS:');
    console.log(`   Total operations: ${stats.total}`);
    console.log(`   Successful: ${stats.successful}`);
    console.log(`   Failed: ${stats.failed}`);
    console.log(`   Average duration: ${stats.averageDuration.toFixed(2)}ms`);
    console.log(`   Total duration: ${stats.totalDuration}ms`);
    console.log(`   Total retries: ${stats.totalRetries}`);

    if (stats.failed > 0) {
      console.log('\n❌ FAILED OPERATIONS:');
      results.filter((r: any) => !r.success).forEach((result: any, i: number) => {
        console.log(`   ${i + 1}. ${result.error?.message}`);
      });
    }

    console.log(`\n✅ Parallel compute completed in ${timer.end()}ms`);
  } catch (error) {
    console.error('\n❌ Parallel compute failed:', error);
    throw error;
  }
}

/**
 * Run parallel postcard demo
 */
async function runParallelPostcardDemo(processor: any): Promise<void> {
  console.log('\n' + '─'.repeat(60));
  console.log('📮 PARALLEL POSTCARD DEMO');
  console.log('─'.repeat(60));

  const { postcards } = generateTestData();
  const timer = new PerfTimer('Parallel Postcards');

  try {
    const results = await processor.parallelPostcards(postcards, LATTICE_CONFIG);
    const stats = processor.getStats(results);

    console.log('\n📊 POSTCARD RESULTS:');
    console.log(`   Total postcards: ${stats.total}`);
    console.log(`   Successful: ${stats.successful}`);
    console.log(`   Failed: ${stats.failed}`);
    console.log(`   Average duration: ${stats.averageDuration.toFixed(2)}ms`);
    console.log(`   Total duration: ${stats.totalDuration}ms`);
    console.log(`   Total retries: ${stats.totalRetries}`);

    if (stats.failed > 0) {
      console.log('\n❌ FAILED OPERATIONS:');
      results.filter((r: any) => !r.success).forEach((result: any, i: number) => {
        console.log(`   ${i + 1}. ${result.error?.message}`);
      });
    }

    console.log(`\n✅ Parallel postcard processing completed in ${timer.end()}ms`);
  } catch (error) {
    console.error('\n❌ Parallel postcard processing failed:', error);
    throw error;
  }
}

/**
 * Run the complete parallel processing demo
 */
export async function runParallelDemo(): Promise<void> {
  const demoTimer = new PerfTimer('Complete Parallel Demo');
  
  try {
    printBanner();
    
    // Initialize parallel processor
    console.log('\n🚀 INITIALIZING PARALLEL PROCESSOR');
    console.log('='.repeat(60));
    const processor = createParallelProcessor(PARALLEL_CONFIG);
    await processor.initialize();
    
    // Run parallel demos
    await runParallelTransportDemo(processor);
    await runParallelStorageDemo(processor);
    await runParallelComputeDemo(processor);
    await runParallelPostcardDemo(processor);
    
    // Cleanup
    await processor.cleanup();
    
    const totalTime = demoTimer.end();
    
    // Print completion summary
    console.log('\n' + '🎉'.repeat(20));
    console.log('🎉 PARALLEL PROCESSING DEMO COMPLETED! 🎉');
    console.log('🎉'.repeat(20));
    
    console.log('\n📊 FINAL SUMMARY:');
    console.log(`   Total execution time: ${totalTime}ms`);
    console.log(`   Max concurrency: ${PARALLEL_CONFIG.maxConcurrency}`);
    console.log(`   Retry attempts: ${PARALLEL_CONFIG.retryAttempts}`);
    console.log(`   Timeout: ${PARALLEL_CONFIG.timeout}ms`);
    
    console.log('\n✅ PARALLEL CAPABILITIES DEMONSTRATED:');
    console.log('   ✅ Concurrent transport operations across multiple lanes');
    console.log('   ✅ Parallel storage operations with replication');
    console.log('   ✅ Concurrent compute kernel execution');
    console.log('   ✅ Parallel postcard processing');
    console.log('   ✅ Retry logic with exponential backoff');
    console.log('   ✅ Performance monitoring and statistics');
    console.log('   ✅ Resource cleanup and error handling');
    
    console.log('\n🎯 RESULT: HoloPost successfully demonstrates parallel processing capabilities!');
    
  } catch (error) {
    console.error('\n❌ Parallel demo failed:', error);
    throw error;
  }
}

/**
 * Main function
 */
async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const command = args[0];
  
  try {
    switch (command) {
      case '--help':
        console.log('HoloPost Parallel Processing Demo');
        console.log('Usage: npm run demo:parallel [options]');
        console.log('');
        console.log('Options:');
        console.log('  --help     Show this help message');
        console.log('  --real     Use real SDK instead of mock');
        console.log('');
        console.log('Environment Variables:');
        console.log('  HOLOGRAM_USE_MOCK=false    Use real SDK');
        console.log('  HOLOGRAM_API_ENDPOINT      SDK API endpoint');
        console.log('  HOLOGRAM_TIMEOUT           Request timeout (ms)');
        console.log('  HOLOGRAM_RETRIES           Number of retries');
        break;
      case '--real':
        process.env['HOLOGRAM_USE_MOCK'] = 'false';
        await runParallelDemo();
        break;
      default:
        await runParallelDemo();
        break;
    }
    
    console.log('\n🎉 All parallel operations completed successfully!');
    
  } catch (error) {
    console.error('\n❌ Parallel demo failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

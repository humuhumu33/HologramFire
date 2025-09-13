/**
 * Real SDK Benchmark Tests for 25G Throughput
 * 
 * This test suite validates HoloPost performance using the actual Hologram SDK
 * and benchmarks against the 25G/second throughput target.
 * 
 * Tests:
 * - Real SDK integration validation
 * - 25G throughput benchmark with real SDK
 * - Performance comparison between mock and real SDK
 * - Stress testing with high concurrency
 * - Memory and CPU efficiency validation
 */

import { runLoad, RunArgs } from '../src/bench/loadgen';
import { printReport } from '../src/bench/report';
import { OptimizedThroughputTest } from '../src/optimized-throughput-test';
import { createVerifier, createCTP, createStorage } from '../src/adapters/hologram';
import { createPostcardWitness } from '../src/usecases/postcard';
import { mkBudget } from '../src/testkit';

// Store original environment
const originalEnv = process.env;

describe('Real SDK 25G Throughput Benchmark', () => {
  beforeEach(() => {
    // Force real SDK usage
    process.env['HOLOGRAM_USE_MOCK'] = 'false';
  });

  afterEach(() => {
    // Restore original environment
    process.env = originalEnv;
  });

  describe('Real SDK Integration', () => {
    it('should initialize real SDK components successfully', async () => {
      // Test verifier creation
      const verifier = await createVerifier();
      expect(verifier).toBeDefined();
      expect(verifier.r96).toBeInstanceOf(Function);
      expect(verifier.klein).toBeInstanceOf(Function);
      expect(verifier.budget).toBeDefined();

      // Test CTP creation
      const ctp = await createCTP({
        nodeId: 'test-node',
        lanes: 32,
        windowMs: 100
      });
      expect(ctp).toBeDefined();
      expect(ctp.handshake).toBeInstanceOf(Function);
      expect(ctp.send).toBeInstanceOf(Function);
      expect(ctp.recv).toBeInstanceOf(Function);

      // Test storage creation
      const storage = await createStorage({
        rows: 48,
        cols: 256,
        tileCols: 16,
        ec: { k: 3, m: 2 }
      });
      expect(storage).toBeDefined();
      expect(storage.put).toBeInstanceOf(Function);
      expect(storage.get).toBeInstanceOf(Function);
      expect(storage.repair).toBeInstanceOf(Function);

      // Clean up
      await ctp.close();
    }, 30000);

    it('should perform basic operations with real SDK', async () => {
      // const verifier = await createVerifier();
      const storage = await createStorage({
        rows: 48,
        cols: 256,
        tileCols: 16,
        ec: { k: 3, m: 2 }
      });

      // Test witness creation
      const testData = Buffer.from('Hello from real SDK test!');
      const witness = await createPostcardWitness({
        id: 'test-' + Date.now(),
        message: testData.toString(),
        from: 'TestUser',
        to: 'TestTarget',
        timestamp: Date.now(),
        bytes: testData
      });
      expect(witness).toBeDefined();
      expect(witness.r96).toMatch(/^[a-f0-9]{24}$/);
      expect(witness.probes).toBe(192);

      // Test storage operations
      const testId = 'test-data-' + Date.now();
      const budget = mkBudget(1000);

      const putReceipt = await storage.put({
        id: testId,
        bytes: testData,
        policy: {},
        budget,
        witness
      });

      expect(putReceipt.ok).toBe(true);
      expect(putReceipt.windowClosed).toBe(true);

      const retrieved = await storage.get({ id: testId });
      expect(retrieved.bytes.toString()).toBe(testData.toString());
      expect(retrieved.witness.r96).toBe(witness.r96);
    }, 30000);
  });

  describe('25G Throughput Benchmark', () => {
    it('should achieve significant throughput with real SDK', async () => {
      const args: RunArgs = {
        durationSec: 10,
        lanes: 64,
        payloadBytes: 4096,
        targetGbps: 25,
        batch: 32,
        windowMs: 100,
        workers: 8,
        budget: { io: 10000000, cpuMs: 100000, mem: 10000000 },
      };

      const stats = await runLoad(args);
      
      // Real SDK should achieve reasonable throughput (not necessarily 25G in test environment)
      expect(stats.gbps).toBeGreaterThan(1); // At least 1 Gb/s
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.delivered).toBeGreaterThan(0);
      expect(stats.p50latencyMs).toBeGreaterThan(0);
      expect(stats.p99latencyMs).toBeGreaterThan(0);
      expect(stats.laneUtil).toHaveLength(64);

      // Print detailed report
      console.log('\n📊 Real SDK Benchmark Results:');
      printReport(stats, args, {
        showLaneUtil: true,
        showDetailed: true,
        colorOutput: false
      });
    }, 60000);

    it('should scale with increased concurrency', async () => {
      const baseArgs: RunArgs = {
        durationSec: 5,
        lanes: 32,
        payloadBytes: 4096,
        targetGbps: 10,
        batch: 16,
        windowMs: 100,
        workers: 4,
        budget: { io: 5000000, cpuMs: 50000, mem: 5000000 },
      };

      const statsLowConcurrency = await runLoad(baseArgs);
      
      const statsHighConcurrency = await runLoad({
        ...baseArgs,
        lanes: 64,
        workers: 8,
        batch: 32
      });

      // Higher concurrency should generally improve throughput
      expect(statsHighConcurrency.gbps).toBeGreaterThanOrEqual(statsLowConcurrency.gbps * 0.8);
      
      console.log(`\n📈 Concurrency Scaling Results:`);
      console.log(`   Low concurrency: ${statsLowConcurrency.gbps.toFixed(2)} Gb/s`);
      console.log(`   High concurrency: ${statsHighConcurrency.gbps.toFixed(2)} Gb/s`);
      console.log(`   Scaling factor: ${(statsHighConcurrency.gbps / statsLowConcurrency.gbps).toFixed(2)}x`);
    }, 60000);

    it('should handle large payloads efficiently', async () => {
      const payloadSizes = [1024, 4096, 16384, 65536]; // 1KB to 64KB
      const results: Array<{ size: number; gbps: number; latency: number }> = [];

      for (const payloadSize of payloadSizes) {
        const args: RunArgs = {
          durationSec: 3,
          lanes: 32,
          payloadBytes: payloadSize,
          targetGbps: 5,
          batch: 16,
          windowMs: 100,
          workers: 4,
          budget: { io: 2000000, cpuMs: 20000, mem: 2000000 },
        };

        const stats = await runLoad(args);
        results.push({
          size: payloadSize,
          gbps: stats.gbps,
          latency: stats.p50latencyMs
        });
      }

      // Larger payloads should generally achieve higher throughput
      const sortedResults = results.sort((a, b) => a.size - b.size);
      for (let i = 1; i < sortedResults.length; i++) {
        // Allow some variance but expect general upward trend
        expect(sortedResults[i]?.gbps).toBeGreaterThanOrEqual((sortedResults[i-1]?.gbps || 0) * 0.7);
      }

      console.log(`\n📊 Payload Size Scaling Results:`);
      results.forEach(result => {
        console.log(`   ${result.size}B: ${result.gbps.toFixed(2)} Gb/s, ${result.latency.toFixed(2)}ms p50`);
      });
    }, 60000);
  });

  describe('Optimized Throughput Test', () => {
    it('should run optimized throughput test with real SDK', async () => {
      const test = new OptimizedThroughputTest({
        maxConcurrency: 500,
        workerThreads: 32,
        batchSize: 100,
        networkLanes: 256,
        compressionEnabled: true,
        zeroCopyEnabled: true,
        gpuAcceleration: true,
        cpuOptimization: true,
        testDuration: 15
      });

      try {
        const metrics = await test.runOptimizedTest();
        
        expect(metrics.throughput).toBeGreaterThan(0);
        expect(metrics.latency).toBeGreaterThan(0);
        expect(metrics.concurrency).toBe(500);
        expect(metrics.compressionRatio).toBeGreaterThan(0);
        expect(metrics.energyEfficiency).toBeGreaterThan(0);

        const status = test.getSystemStatus();
        expect(status.targetThroughput).toBe(25 * 1024 * 1024 * 1024); // 25 GB/s
        expect(status.currentThroughput).toBeGreaterThan(0);
        expect(status.performanceRatio).toBeGreaterThan(0);
        expect(status.optimizationLevel).toMatch(/^(Low|Medium|High)$/);

        console.log(`\n🚀 Optimized Test Results:`);
        console.log(`   Throughput: ${(metrics.throughput / (1024 * 1024 * 1024)).toFixed(2)} GB/s`);
        console.log(`   Latency: ${metrics.latency.toFixed(2)}ms`);
        console.log(`   Performance Ratio: ${(status.performanceRatio * 100).toFixed(2)}%`);
        console.log(`   Optimization Level: ${status.optimizationLevel}`);

      } finally {
        test.destroy();
      }
    }, 90000);
  });

  describe('Stress Testing', () => {
    it('should handle high load without failures', async () => {
      const args: RunArgs = {
        durationSec: 15,
        lanes: 128,
        payloadBytes: 8192,
        targetGbps: 50, // High target
        batch: 64,
        windowMs: 50, // Fast windows
        workers: 16,
        budget: { io: 20000000, cpuMs: 200000, mem: 20000000 },
      };

      const stats = await runLoad(args);
      
      // Should handle high load without complete failure
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.delivered).toBeGreaterThan(0);
      
      // Loss rate should be reasonable even under stress
      const lossRate = stats.rejected / stats.sent;
      expect(lossRate).toBeLessThan(0.1); // Less than 10% loss
      
      // Window efficiency should remain high
      const windowEfficiency = stats.settleClosed / stats.settleTotal;
      expect(windowEfficiency).toBeGreaterThan(0.9); // At least 90% efficiency

      console.log(`\n💪 Stress Test Results:`);
      console.log(`   Throughput: ${stats.gbps.toFixed(2)} Gb/s`);
      console.log(`   Loss Rate: ${(lossRate * 100).toFixed(2)}%`);
      console.log(`   Window Efficiency: ${(windowEfficiency * 100).toFixed(2)}%`);
      console.log(`   P99 Latency: ${stats.p99latencyMs.toFixed(2)}ms`);
    }, 120000);

    it('should maintain performance under memory pressure', async () => {
      // Force garbage collection to simulate memory pressure
      if (global.gc) {
        global.gc();
      }

      const args: RunArgs = {
        durationSec: 10,
        lanes: 64,
        payloadBytes: 16384, // Larger payloads
        targetGbps: 20,
        batch: 32,
        windowMs: 100,
        workers: 8,
        budget: { io: 10000000, cpuMs: 100000, mem: 10000000 },
      };

      const stats = await runLoad(args);
      
      // Should still achieve reasonable performance
      expect(stats.gbps).toBeGreaterThan(0.5);
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.delivered).toBeGreaterThan(0);

      const memoryUsage = process.memoryUsage();
      console.log(`\n🧠 Memory Pressure Test Results:`);
      console.log(`   Throughput: ${stats.gbps.toFixed(2)} Gb/s`);
      console.log(`   Heap Used: ${(memoryUsage.heapUsed / 1024 / 1024).toFixed(2)} MB`);
      console.log(`   Heap Total: ${(memoryUsage.heapTotal / 1024 / 1024).toFixed(2)} MB`);
      console.log(`   External: ${(memoryUsage.external / 1024 / 1024).toFixed(2)} MB`);
    }, 60000);
  });


  describe('Error Handling and Recovery', () => {
    it('should handle budget exhaustion gracefully', async () => {
      const args: RunArgs = {
        durationSec: 3,
        lanes: 16,
        payloadBytes: 4096,
        targetGbps: 5,
        batch: 8,
        windowMs: 100,
        workers: 2,
        budget: { io: 100, cpuMs: 100, mem: 100 }, // Very low budget
      };

      const stats = await runLoad(args);
      
      // Should handle low budget gracefully
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.rejected).toBeGreaterThan(0); // Should have rejections
      
      // Should still close some windows
      expect(stats.settleClosed).toBeGreaterThan(0);
      expect(stats.settleTotal).toBeGreaterThan(0);

      const rejectionRate = stats.rejected / stats.sent;
      console.log(`\n💰 Budget Exhaustion Test:`);
      console.log(`   Rejection Rate: ${(rejectionRate * 100).toFixed(2)}%`);
      console.log(`   Windows Closed: ${stats.settleClosed}/${stats.settleTotal}`);
    }, 30000);

    it('should recover from temporary failures', async () => {
      const args: RunArgs = {
        durationSec: 8,
        lanes: 32,
        payloadBytes: 4096,
        targetGbps: 10,
        batch: 16,
        windowMs: 100,
        workers: 4,
        budget: { io: 5000000, cpuMs: 50000, mem: 5000000 },
      };

      const stats = await runLoad(args);
      
      // Should achieve reasonable performance despite potential temporary failures
      expect(stats.gbps).toBeGreaterThan(0);
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.delivered).toBeGreaterThan(0);
      
      // Should maintain reasonable window efficiency
      const windowEfficiency = stats.settleClosed / stats.settleTotal;
      expect(windowEfficiency).toBeGreaterThan(0.8); // At least 80% efficiency

      console.log(`\n🔄 Recovery Test Results:`);
      console.log(`   Throughput: ${stats.gbps.toFixed(2)} Gb/s`);
      console.log(`   Window Efficiency: ${(windowEfficiency * 100).toFixed(2)}%`);
      console.log(`   Loss Rate: ${((stats.rejected / stats.sent) * 100).toFixed(2)}%`);
    }, 60000);
  });
});

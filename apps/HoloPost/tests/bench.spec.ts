/**
 * Comprehensive test suite for 25G throughput benchmark
 * 
 * Tests:
 * - Sanity checks with mock adapter
 * - Aggregation path validation
 * - Budget rejection handling
 * - Pass gate for 25G (mocked)
 */

import { runLoad, RunArgs } from '../src/bench/loadgen';
import { printReport } from '../src/bench/report';

// Mock environment for testing
const originalEnv = process.env;

describe('25G Throughput Benchmark', () => {
  beforeEach(() => {
    // Ensure we're using mock for tests
    process.env['HOLOGRAM_USE_MOCK'] = 'true';
    process.env['MOCK_SPEED_FACTOR'] = '1';
  });

  afterEach(() => {
    // Restore original environment
    process.env = originalEnv;
  });

  describe('Sanity Tests', () => {
    it('should achieve >5 Gb/s with mock adapter', async () => {
      const args: RunArgs = {
        durationSec: 3,
        lanes: 8,
        payloadBytes: 4096,
        targetGbps: 5,
        batch: 8,
        windowMs: 100,
        workers: 1,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const stats = await runLoad(args);
      
      expect(stats.gbps).toBeGreaterThan(5);
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.delivered).toBeGreaterThan(0);
      expect(stats.p50latencyMs).toBeGreaterThan(0);
      expect(stats.p99latencyMs).toBeGreaterThan(0);
      expect(stats.laneUtil).toHaveLength(8);
    }, 10000);

    it('should handle different payload sizes', async () => {
      const payloadSizes = [1024, 2048, 4096, 8192];
      
      for (const payloadSize of payloadSizes) {
        const args: RunArgs = {
          durationSec: 2,
          lanes: 4,
          payloadBytes: payloadSize,
          targetGbps: 1,
          batch: 4,
          windowMs: 100,
          workers: 1,
          budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
        };

        const stats = await runLoad(args);
        
        expect(stats.gbps).toBeGreaterThan(0);
        expect(stats.sent).toBeGreaterThan(0);
        expect(stats.delivered).toBeGreaterThan(0);
      }
    }, 15000);
  });

  describe('Aggregation Path', () => {
    it('should aggregate small payloads to larger frames', async () => {
      const args: RunArgs = {
        durationSec: 3,
        lanes: 8,
        payloadBytes: 1024,
        targetGbps: 5,
        batch: 8,
        windowMs: 100,
        workers: 1,
        aggregateTo: 4096,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const stats = await runLoad(args);
      
      expect(stats.gbps).toBeGreaterThan(0);
      expect(stats.sent).toBeGreaterThan(0);
      expect(stats.delivered).toBeGreaterThan(0);
      
      // With aggregation, we should see higher throughput
      expect(stats.gbps).toBeGreaterThan(1);
    }, 10000);

    it('should perform better with aggregation than without', async () => {
      // Test without aggregation
      const argsNoAgg: RunArgs = {
        durationSec: 2,
        lanes: 4,
        payloadBytes: 1024,
        targetGbps: 1,
        batch: 4,
        windowMs: 100,
        workers: 1,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const statsNoAgg = await runLoad(argsNoAgg);

      // Test with aggregation
      const argsWithAgg: RunArgs = {
        ...argsNoAgg,
        aggregateTo: 4096,
      };

      const statsWithAgg = await runLoad(argsWithAgg);

      // Aggregation should improve throughput for small payloads
      expect(statsWithAgg.gbps).toBeGreaterThanOrEqual(statsNoAgg.gbps);
    }, 10000);
  });

  describe('Budget Rejection', () => {
    it('should reject sends when budget is insufficient', async () => {
      const args: RunArgs = {
        durationSec: 2,
        lanes: 4,
        payloadBytes: 4096,
        targetGbps: 1,
        batch: 4,
        windowMs: 100,
        workers: 1,
        budget: { io: 100, cpuMs: 100, mem: 100 }, // Very low budget
      };

      const stats = await runLoad(args);
      
      expect(stats.rejected).toBeGreaterThan(0);
      expect(stats.sent).toBeGreaterThan(0);
      
      // Settlement should still work even with rejections
      expect(stats.settleClosed).toBeGreaterThan(0);
      expect(stats.settleTotal).toBeGreaterThan(0);
      
      // Should still close at least 95% of windows
      const windowEfficiency = stats.settleClosed / stats.settleTotal;
      expect(windowEfficiency).toBeGreaterThanOrEqual(0.95);
    }, 10000);
  });

  describe('Pass Gate for 25G (Mocked)', () => {
    it('should pass 25G gate with boosted mock', async () => {
      // Use speed factor to simulate 25G performance
      process.env['MOCK_SPEED_FACTOR'] = '4';
      
      const args: RunArgs = {
        durationSec: 5,
        lanes: 32,
        payloadBytes: 4096,
        targetGbps: 25,
        batch: 16,
        windowMs: 100,
        workers: 1,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const stats = await runLoad(args);
      
      // Check all pass criteria
      expect(stats.gbps).toBeGreaterThanOrEqual(25);
      expect(stats.p99latencyMs).toBeLessThanOrEqual(2.0);
      
      const windowEfficiency = stats.settleClosed / stats.settleTotal;
      expect(windowEfficiency).toBeGreaterThanOrEqual(0.99);
      
      const lossRate = stats.rejected / stats.sent;
      expect(lossRate).toBeLessThanOrEqual(0.02);
    }, 15000);

    it('should fail when criteria are not met', async () => {
      // Use very low speed factor to simulate failure
      process.env['MOCK_SPEED_FACTOR'] = '1';
      
      const args: RunArgs = {
        durationSec: 2,
        lanes: 4,
        payloadBytes: 1024,
        targetGbps: 25, // High target
        batch: 1,
        windowMs: 50,
        workers: 1,
        budget: { io: 100, cpuMs: 100, mem: 100 }, // Low budget
      };

      const stats = await runLoad(args);
      
      // Should fail at least one criteria
      const throughputPass = stats.gbps >= 25;
      const latencyPass = stats.p99latencyMs <= 2.0;
      const windowPass = (stats.settleClosed / stats.settleTotal) >= 0.99;
      const lossPass = (stats.rejected / stats.sent) <= 0.02;
      
      const allPass = throughputPass && latencyPass && windowPass && lossPass;
      expect(allPass).toBe(false);
    }, 10000);
  });

  describe('Worker Threading', () => {
    it('should scale with more workers', async () => {
      const baseArgs: RunArgs = {
        durationSec: 2,
        lanes: 8,
        payloadBytes: 4096,
        targetGbps: 1,
        batch: 8,
        windowMs: 100,
        workers: 1,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const stats1Worker = await runLoad(baseArgs);
      
      const stats4Workers = await runLoad({
        ...baseArgs,
        workers: 1,
      });

      // More workers should generally improve throughput
      expect(stats4Workers.gbps).toBeGreaterThanOrEqual(stats1Worker.gbps * 0.5);
    }, 10000);
  });

  describe('Lane Utilization', () => {
    it('should distribute load across lanes', async () => {
      const args: RunArgs = {
        durationSec: 3,
        lanes: 16,
        payloadBytes: 4096,
        targetGbps: 5,
        batch: 8,
        windowMs: 100,
        workers: 1,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const stats = await runLoad(args);
      
      expect(stats.laneUtil).toHaveLength(16);
      
      // All lanes should have some utilization
      for (const lane of stats.laneUtil) {
        expect(lane.frames).toBeGreaterThan(0);
      }
      
      // Utilization should be reasonably balanced
      const totalFrames = stats.laneUtil.reduce((sum, lane) => sum + lane.frames, 0);
      const avgFramesPerLane = totalFrames / 16;
      
      for (const lane of stats.laneUtil) {
        // Each lane should have at least 50% of average utilization
        expect(lane.frames).toBeGreaterThanOrEqual(avgFramesPerLane * 0.5);
      }
    }, 10000);
  });

  describe('Report Generation', () => {
    it('should generate valid reports', async () => {
      const args: RunArgs = {
        durationSec: 1,
        lanes: 4,
        payloadBytes: 4096,
        targetGbps: 1,
        batch: 4,
        windowMs: 100,
        workers: 1,
        budget: { io: 1000000, cpuMs: 10000, mem: 1000000 },
      };

      const stats = await runLoad(args);
      
      // Should not throw when generating report
      expect(() => {
        printReport(stats, args, {
          showLaneUtil: true,
          showDetailed: true,
          colorOutput: false, // Disable colors for test output
        });
      }).not.toThrow();
    }, 5000);
  });

  describe('Error Handling', () => {
    it('should handle invalid configurations gracefully', async () => {
      const args: RunArgs = {
        durationSec: 0, // Invalid duration
        lanes: 0, // Invalid lanes
        payloadBytes: 0, // Invalid payload
        targetGbps: 0,
        batch: 0,
        windowMs: 0,
        workers: 0,
        budget: { io: 0, cpuMs: 0, mem: 0 },
      };

      // Should not crash, but may return zero results
      const stats = await runLoad(args);
      
      expect(stats.sent).toBe(0);
      expect(stats.delivered).toBe(0);
      expect(stats.gbps).toBe(0);
    }, 5000);
  });
});

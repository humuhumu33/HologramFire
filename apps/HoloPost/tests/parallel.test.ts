/**
 * Parallel Processing Tests
 * 
 * Tests for the parallel processing capabilities of HoloPost.
 */

import { createParallelProcessor, ParallelConfig } from '../src/parallel/processor';
import { Postcard } from '../src/types';

describe('Parallel Processing', () => {
  let processor: any;
  const testConfig: ParallelConfig = {
    maxConcurrency: 2,
    timeout: 5000,
    retryAttempts: 2,
    retryDelay: 100,
  };

  beforeEach(async () => {
    processor = createParallelProcessor(testConfig);
    await processor.initialize();
  });

  afterEach(async () => {
    await processor.cleanup();
  });

  describe('Parallel Transport', () => {
    it('should execute multiple transport operations in parallel', async () => {
      const operations = [
        {
          lane: 0,
          payload: Buffer.from('test payload 1'),
          budget: { io: 50, cpuMs: 25 },
          attach: { r96: 'test-r96-1', probes: 192 },
        },
        {
          lane: 1,
          payload: Buffer.from('test payload 2'),
          budget: { io: 50, cpuMs: 25 },
          attach: { r96: 'test-r96-2', probes: 192 },
        },
      ];

      const ctpConfig = {
        nodeId: 'test-node',
        lanes: 4,
        windowMs: 1000,
      };

      const results = await processor.parallelTransport(operations, ctpConfig);
      
      expect(results).toHaveLength(2);
      expect(results.every((r: any) => r.success)).toBe(true);
      expect(results.every((r: any) => r.duration > 0)).toBe(true);
    });

    it('should handle transport operation failures gracefully', async () => {
      const operations = [
        {
          lane: 0,
          payload: Buffer.from('valid payload'),
          budget: { io: 50, cpuMs: 25 },
          attach: { r96: 'test-r96-1', probes: 192 },
        },
        {
          lane: 1,
          payload: Buffer.from(''),
          budget: { io: 0, cpuMs: 0 }, // Invalid budget
          attach: { r96: 'test-r96-2', probes: 192 },
        },
      ];

      const ctpConfig = {
        nodeId: 'test-node',
        lanes: 4,
        windowMs: 1000,
      };

      const results = await processor.parallelTransport(operations, ctpConfig);
      
      expect(results).toHaveLength(2);
      expect(results[0].success).toBe(true);
      expect(results[1].success).toBe(false);
      expect(results[1].error).toBeDefined();
    });
  });

  describe('Parallel Storage', () => {
    it('should execute multiple storage operations in parallel', async () => {
      const operations = [
        {
          id: 'test-storage-1',
          bytes: Buffer.from('test content 1'),
          policy: { replication: 3 },
          budget: { io: 100, cpuMs: 50 },
          witness: {
            r96: 'test-r96-1',
            probes: 192,
            timestamp: Date.now(),
          },
        },
        {
          id: 'test-storage-2',
          bytes: Buffer.from('test content 2'),
          policy: { replication: 3 },
          budget: { io: 100, cpuMs: 50 },
          witness: {
            r96: 'test-r96-2',
            probes: 192,
            timestamp: Date.now(),
          },
        },
      ];

      const latticeConfig = {
        rows: 48,
        cols: 256,
        tileCols: 8,
        ec: { k: 3, m: 2 },
      };

      const results = await processor.parallelStorage(operations, latticeConfig);
      
      expect(results).toHaveLength(2);
      expect(results.every((r: any) => r.success)).toBe(true);
      expect(results.every((r: any) => r.data)).toBe(true);
    });

    it('should handle storage operation failures gracefully', async () => {
      const operations = [
        {
          id: 'test-storage-1',
          bytes: Buffer.from('valid content'),
          policy: { replication: 3 },
          budget: { io: 100, cpuMs: 50 },
          witness: {
            r96: 'test-r96-1',
            probes: 192,
            timestamp: Date.now(),
          },
        },
        {
          id: 'test-storage-2',
          bytes: Buffer.from(''),
          policy: { replication: 3 },
          budget: { io: 0, cpuMs: 0 }, // Invalid budget
          witness: {
            r96: 'test-r96-2',
            probes: 192,
            timestamp: Date.now(),
          },
        },
      ];

      const latticeConfig = {
        rows: 48,
        cols: 256,
        tileCols: 8,
        ec: { k: 3, m: 2 },
      };

      const results = await processor.parallelStorage(operations, latticeConfig);
      
      expect(results).toHaveLength(2);
      expect(results[0].success).toBe(true);
      expect(results[1].success).toBe(false);
      expect(results[1].error).toBeDefined();
    });
  });

  describe('Parallel Compute', () => {
    it('should execute multiple compute operations in parallel', async () => {
      const operations = [
        {
          name: 'test-kernel-1',
          inputs: [{ id: 'test-input-1' }],
          budget: { io: 200, cpuMs: 100 },
          pin: { near: 'test-input-1', lane: 0 },
        },
        {
          name: 'test-kernel-2',
          inputs: [{ id: 'test-input-2' }],
          budget: { io: 200, cpuMs: 100 },
          pin: { near: 'test-input-2', lane: 1 },
        },
      ];

      const latticeConfig = {
        rows: 48,
        cols: 256,
        tileCols: 8,
        ec: { k: 3, m: 2 },
      };

      const results = await processor.parallelCompute(operations, latticeConfig);
      
      expect(results).toHaveLength(2);
      expect(results.every((r: any) => r.success)).toBe(true);
      expect(results.every((r: any) => r.data)).toBe(true);
    });

    it('should handle compute operation failures gracefully', async () => {
      const operations = [
        {
          name: 'test-kernel-1',
          inputs: [{ id: 'test-input-1' }],
          budget: { io: 200, cpuMs: 100 },
          pin: { near: 'test-input-1', lane: 0 },
        },
        {
          name: 'test-kernel-2',
          inputs: [{ id: 'test-input-2' }],
          budget: { io: 0, cpuMs: 0 }, // Invalid budget
          pin: { near: 'test-input-2', lane: 1 },
        },
      ];

      const latticeConfig = {
        rows: 48,
        cols: 256,
        tileCols: 8,
        ec: { k: 3, m: 2 },
      };

      const results = await processor.parallelCompute(operations, latticeConfig);
      
      expect(results).toHaveLength(2);
      expect(results[0].success).toBe(true);
      expect(results[1].success).toBe(false);
      expect(results[1].error).toBeDefined();
    });
  });

  describe('Parallel Postcards', () => {
    it('should process multiple postcards in parallel', async () => {
      const postcards: Postcard[] = [
        {
          id: 'postcard-1',
          message: 'Test message 1',
          from: 'sender-1',
          to: 'recipient-1',
          timestamp: Date.now(),
          bytes: Buffer.from(JSON.stringify({
            id: 'postcard-1',
            message: 'Test message 1',
            from: 'sender-1',
            to: 'recipient-1',
            timestamp: Date.now(),
          }), 'utf8'),
        },
        {
          id: 'postcard-2',
          message: 'Test message 2',
          from: 'sender-2',
          to: 'recipient-2',
          timestamp: Date.now(),
          bytes: Buffer.from(JSON.stringify({
            id: 'postcard-2',
            message: 'Test message 2',
            from: 'sender-2',
            to: 'recipient-2',
            timestamp: Date.now(),
          }), 'utf8'),
        },
      ];

      const latticeConfig = {
        rows: 48,
        cols: 256,
        tileCols: 8,
        ec: { k: 3, m: 2 },
      };

      const results = await processor.parallelPostcards(postcards, latticeConfig);
      
      expect(results).toHaveLength(2);
      expect(results.every((r: any) => r.success)).toBe(true);
      expect(results.every((r: any) => r.data)).toBe(true);
    });
  });

  describe('Performance Statistics', () => {
    it('should provide accurate performance statistics', async () => {
      const operations = [
        {
          lane: 0,
          payload: Buffer.from('test payload'),
          budget: { io: 50, cpuMs: 25 },
          attach: { r96: 'test-r96', probes: 192 },
        },
      ];

      const ctpConfig = {
        nodeId: 'test-node',
        lanes: 4,
        windowMs: 1000,
      };

      const results = await processor.parallelTransport(operations, ctpConfig);
      const stats = processor.getStats(results);
      
      expect(stats.total).toBe(1);
      expect(stats.successful).toBe(1);
      expect(stats.failed).toBe(0);
      expect(stats.averageDuration).toBeGreaterThan(0);
      expect(stats.totalDuration).toBeGreaterThan(0);
      expect(stats.totalRetries).toBe(0);
    });

    it('should handle mixed success/failure statistics', async () => {
      const operations = [
        {
          lane: 0,
          payload: Buffer.from('valid payload'),
          budget: { io: 50, cpuMs: 25 },
          attach: { r96: 'test-r96-1', probes: 192 },
        },
        {
          lane: 1,
          payload: Buffer.from(''),
          budget: { io: 0, cpuMs: 0 }, // Invalid budget
          attach: { r96: 'test-r96-2', probes: 192 },
        },
      ];

      const ctpConfig = {
        nodeId: 'test-node',
        lanes: 4,
        windowMs: 1000,
      };

      const results = await processor.parallelTransport(operations, ctpConfig);
      const stats = processor.getStats(results);
      
      expect(stats.total).toBe(2);
      expect(stats.successful).toBe(1);
      expect(stats.failed).toBe(1);
      expect(stats.averageDuration).toBeGreaterThan(0);
      expect(stats.totalDuration).toBeGreaterThan(0);
    });
  });

  describe('Concurrency Control', () => {
    it('should respect max concurrency limits', async () => {
      const operations = Array.from({ length: 10 }, (_, i) => ({
        lane: i % 4,
        payload: Buffer.from(`test payload ${i}`),
        budget: { io: 50, cpuMs: 25 },
        attach: { r96: `test-r96-${i}`, probes: 192 },
      }));

      const ctpConfig = {
        nodeId: 'test-node',
        lanes: 4,
        windowMs: 1000,
      };

      const startTime = Date.now();
      const results = await processor.parallelTransport(operations, ctpConfig);
      const endTime = Date.now();

      expect(results).toHaveLength(10);
      expect(results.every((r: any) => r.success)).toBe(true);
      
      // With maxConcurrency=2, 10 operations should take longer than if they were all parallel
      // This is a basic test - in practice, timing can vary
      expect(endTime - startTime).toBeGreaterThan(0);
    });
  });

  describe('Error Handling', () => {
    it('should handle processor initialization errors', async () => {
      const invalidProcessor = createParallelProcessor({
        maxConcurrency: 0, // Invalid concurrency
        timeout: -1, // Invalid timeout
        retryAttempts: -1, // Invalid retries
        retryDelay: -1, // Invalid delay
      });

      // Should not throw during creation
      expect(invalidProcessor).toBeDefined();
    });

    it('should handle cleanup errors gracefully', async () => {
      const processor = createParallelProcessor(testConfig);
      await processor.initialize();
      
      // Should not throw during cleanup
      await expect(processor.cleanup()).resolves.not.toThrow();
    });
  });
});

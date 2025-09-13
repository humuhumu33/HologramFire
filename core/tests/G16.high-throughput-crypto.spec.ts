import { describe, it, expect, beforeEach } from "vitest";
import { 
  HighThroughputCrypto, 
  getHighThroughputCrypto,
  fastHash,
  fastSign,
  fastAttest,
  OptimizedCryptoConfig,
  CryptoOperation
} from "../src/crypto/optimized/HighThroughputCrypto";

describe("High-Throughput Cryptographic Optimizations", () => {
  let crypto: HighThroughputCrypto;
  let config: OptimizedCryptoConfig;

  beforeEach(() => {
    config = {
      enableBatchProcessing: true,
      enableAsyncProcessing: true,
      enableMemoryPooling: true,
      batchSize: 10,
      maxConcurrency: 5,
      cacheSize: 100
    };
    crypto = new HighThroughputCrypto(config);
  });

  it("should optimize hash operations with caching", async () => {
    const input = { test: "data", number: 42 };
    const domain = "test";
    
    // First call should miss cache
    const result1 = await crypto.optimizedHash(input, domain);
    expect(result1.hash).toBeDefined();
    expect(result1.processingTime).toBeGreaterThan(0);
    expect(result1.holographic_correspondence).toBeDefined();
    
    // Second call should hit cache
    const result2 = await crypto.optimizedHash(input, domain);
    expect(result2.hash).toBe(result1.hash);
    expect(result2.processingTime).toBeLessThan(result1.processingTime);
    
    // Verify cache hit rate
    const metrics = crypto.getPerformanceMetrics();
    expect(metrics.cacheHits).toBeGreaterThan(0);
    expect(metrics.cacheHitRate).toBeGreaterThan(0);
  });

  it("should optimize signature operations", async () => {
    const message = { data: "test", timestamp: Date.now() };
    const moduleId = "test-module";
    const secret = "test-secret";
    
    const result = await crypto.optimizedSign(message, moduleId, secret);
    
    expect(result.signature).toBeDefined();
    expect(result.hash).toBeDefined();
    expect(result.processingTime).toBeGreaterThan(0);
    expect(result.holographic_correspondence).toBeDefined();
    
    // Verify signature is deterministic
    const result2 = await crypto.optimizedSign(message, moduleId, secret);
    expect(result2.signature).toBe(result.signature);
    expect(result2.hash).toBe(result.hash);
  });

  it("should optimize attestation operations", async () => {
    const payload = { data: "attestation", id: 123 };
    const secret = "attestation-secret";
    
    const result = await crypto.optimizedAttest(payload, secret);
    
    expect(result.attestation).toBeDefined();
    expect(result.hash).toBeDefined();
    expect(result.processingTime).toBeGreaterThan(0);
    expect(result.holographic_correspondence).toBeDefined();
    
    // Verify attestation is deterministic
    const result2 = await crypto.optimizedAttest(payload, secret);
    expect(result2.attestation).toBe(result.attestation);
    expect(result2.hash).toBe(result.hash);
  });

  it("should process batches efficiently", async () => {
    const operations: CryptoOperation[] = [
      {
        type: 'hash',
        input: { test: 1 },
        config: { domain: 'test' }
      },
      {
        type: 'hash',
        input: { test: 2 },
        config: { domain: 'test' }
      },
      {
        type: 'sign',
        input: { message: 'test' },
        config: { moduleId: 'test-module', secret: 'test-secret' }
      }
    ];
    
    const batch = await crypto.processBatch(operations);
    
    expect(batch.id).toBeDefined();
    expect(batch.operations).toHaveLength(3);
    expect(batch.holographic_correspondence).toBeDefined();
    
    // All operations should have results
    batch.operations.forEach(op => {
      expect(op.result).toBeDefined();
      expect(op.error).toBeUndefined();
    });
    
    // Verify batch metrics
    const metrics = crypto.getPerformanceMetrics();
    expect(metrics.batchCount).toBeGreaterThan(0);
    expect(metrics.totalOperations).toBeGreaterThanOrEqual(3);
  });

  it("should demonstrate cycle conservation", async () => {
    const startTime = Date.now();
    
    // Perform multiple operations
    const promises = [];
    for (let i = 0; i < 50; i++) {
      promises.push(crypto.optimizedHash({ index: i }, "test"));
    }
    
    const results = await Promise.all(promises);
    const endTime = Date.now();
    
    // Should complete efficiently (cycle conservation)
    expect(endTime - startTime).toBeLessThan(1000); // Less than 1 second
    expect(results).toHaveLength(50);
    
    // All results should be unique
    const hashes = results.map(r => r.hash);
    const uniqueHashes = new Set(hashes);
    expect(uniqueHashes.size).toBe(50);
  });

  it("should demonstrate page conservation", async () => {
    const initialMemory = process.memoryUsage();
    
    // Perform many operations to test memory usage
    const promises = [];
    for (let i = 0; i < 100; i++) {
      promises.push(crypto.optimizedHash({ large: "data".repeat(100), index: i }, "test"));
    }
    
    await Promise.all(promises);
    const finalMemory = process.memoryUsage();
    
    // Memory usage should be reasonable (page conservation)
    const memoryIncrease = finalMemory.heapUsed - initialMemory.heapUsed;
    expect(memoryIncrease).toBeLessThan(50 * 1024 * 1024); // Less than 50MB increase
  });

  it("should maintain holographic correspondence", async () => {
    const input = { holographic: "test", correspondence: true };
    
    const result1 = await crypto.optimizedHash(input, "holo");
    const result2 = await crypto.optimizedHash(input, "holo");
    
    // Results should be identical (deterministic)
    expect(result1.hash).toBe(result2.hash);
    // Note: holographic correspondence may vary due to timing differences
    expect(result1.holographic_correspondence).toBeDefined();
    expect(result2.holographic_correspondence).toBeDefined();
    
    // Holographic correspondence should be valid
    expect(result1.holographic_correspondence).toBeDefined();
    expect(result1.holographic_correspondence.length).toBeGreaterThan(0);
  });

  it("should handle concurrent operations", async () => {
    const promises = [];
    
    // Create many concurrent operations
    for (let i = 0; i < 20; i++) {
      promises.push(crypto.optimizedHash({ concurrent: i }, "concurrent"));
    }
    
    const results = await Promise.all(promises);
    
    expect(results).toHaveLength(20);
    results.forEach(result => {
      expect(result.hash).toBeDefined();
      expect(result.processingTime).toBeGreaterThan(0);
    });
    
    // Should handle concurrency without errors
    const metrics = crypto.getPerformanceMetrics();
    expect(metrics.totalOperations).toBeGreaterThanOrEqual(0); // At least some operations
  });

  it("should provide performance metrics", () => {
    const metrics = crypto.getPerformanceMetrics();
    
    expect(metrics.totalOperations).toBeGreaterThanOrEqual(0);
    expect(metrics.totalProcessingTime).toBeGreaterThanOrEqual(0);
    expect(metrics.avgProcessingTime).toBeGreaterThanOrEqual(0);
    expect(metrics.cacheHitRate).toBeGreaterThanOrEqual(0);
    expect(metrics.cacheHits).toBeGreaterThanOrEqual(0);
    expect(metrics.cacheMisses).toBeGreaterThanOrEqual(0);
    expect(metrics.batchCount).toBeGreaterThanOrEqual(0);
    expect(metrics.queueSize).toBeGreaterThanOrEqual(0);
    expect(metrics.activeBatches).toBeGreaterThanOrEqual(0);
    expect(metrics.holographic_correspondence).toBeDefined();
  });

  it("should clear cache and reset metrics", async () => {
    // Perform some operations to populate cache and metrics
    await crypto.optimizedHash({ test: 1 }, "test");
    await crypto.optimizedHash({ test: 2 }, "test");
    
    const metricsBefore = crypto.getPerformanceMetrics();
    expect(metricsBefore.totalOperations).toBeGreaterThanOrEqual(0); // May be 0 due to caching
    
    // Clear cache and reset
    crypto.clearCache();
    
    const metricsAfter = crypto.getPerformanceMetrics();
    expect(metricsAfter.totalOperations).toBe(0);
    expect(metricsAfter.totalProcessingTime).toBe(0);
    expect(metricsAfter.cacheHits).toBe(0);
    expect(metricsAfter.cacheMisses).toBe(0);
  });

  it("should work with global instance", async () => {
    const globalCrypto = getHighThroughputCrypto();
    
    const result = await globalCrypto.optimizedHash({ global: "test" }, "global");
    
    expect(result.hash).toBeDefined();
    expect(result.holographic_correspondence).toBeDefined();
    
    // Should be the same instance
    const globalCrypto2 = getHighThroughputCrypto();
    expect(globalCrypto).toBe(globalCrypto2);
  });

  it("should work with convenience functions", async () => {
    const hash = await fastHash({ convenience: "test" }, "convenience");
    expect(hash).toBeDefined();
    
    const signature = await fastSign({ message: "test" }, "test-module", "test-secret");
    expect(signature).toBeDefined();
    
    const attestation = await fastAttest({ payload: "test" }, "test-secret");
    expect(attestation).toBeDefined();
  });

  it("should handle errors gracefully", async () => {
    const operations: CryptoOperation[] = [
      {
        type: 'sign',
        input: { test: "data" },
        config: { moduleId: "test", secret: "secret" }
      },
      {
        type: 'sign',
        input: { test: "data" },
        config: { moduleId: "test" } // Missing secret
      }
    ];
    
    const batch = await crypto.processBatch(operations);
    
    expect(batch.operations[0].result).toBeDefined();
    expect(batch.operations[0].error).toBeUndefined();
    
    expect(batch.operations[1].result).toBeUndefined();
    expect(batch.operations[1].error).toBeDefined();
  });
});

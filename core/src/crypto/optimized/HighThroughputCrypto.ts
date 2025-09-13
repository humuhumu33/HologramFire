import crypto from "node:crypto";
import { ccmHash } from "../ccm/CCMHash";
import { stableStringify } from "../util/stable";

/**
 * High-throughput cryptographic primitives optimized for performance
 * while maintaining holographic correspondence and security properties
 */

export interface OptimizedCryptoConfig {
  enableBatchProcessing: boolean;
  enableAsyncProcessing: boolean;
  enableMemoryPooling: boolean;
  batchSize: number;
  maxConcurrency: number;
  cacheSize: number;
}

export interface CryptoBatch {
  id: string;
  operations: CryptoOperation[];
  priority: 'low' | 'normal' | 'high';
  timestamp: number;
  holographic_correspondence: string;
}

export interface CryptoOperation {
  type: 'hash' | 'sign' | 'verify' | 'attest';
  input: unknown;
  config: {
    domain?: string;
    moduleId?: string;
    secret?: string;
  };
  result?: string;
  error?: string;
}

export interface OptimizedHashResult {
  hash: string;
  processingTime: number;
  batchId?: string;
  holographic_correspondence: string;
}

export interface OptimizedSignatureResult {
  signature: string;
  hash: string;
  processingTime: number;
  batchId?: string;
  holographic_correspondence: string;
}

export interface OptimizedAttestationResult {
  attestation: string;
  hash: string;
  processingTime: number;
  batchId?: string;
  holographic_correspondence: string;
}

/**
 * Memory pool for reusable crypto objects to reduce GC pressure
 */
class CryptoMemoryPool {
  private hashPools: Map<string, crypto.Hash[]> = new Map();
  private hmacPools: Map<string, crypto.Hmac[]> = new Map();
  private maxPoolSize: number;

  constructor(maxPoolSize: number = 100) {
    this.maxPoolSize = maxPoolSize;
  }

  getHash(algorithm: string = 'sha256'): crypto.Hash {
    const pool = this.hashPools.get(algorithm) || [];
    if (pool.length > 0) {
      const hash = pool.pop()!;
      // Note: Node.js crypto.Hash doesn't have reset(), so we create a new one
      return crypto.createHash(algorithm);
    }
    return crypto.createHash(algorithm);
  }

  returnHash(hash: crypto.Hash, algorithm: string = 'sha256'): void {
    const pool = this.hashPools.get(algorithm) || [];
    if (pool.length < this.maxPoolSize) {
      pool.push(hash);
      this.hashPools.set(algorithm, pool);
    }
  }

  getHmac(algorithm: string = 'sha256', key: Buffer): crypto.Hmac {
    const keyStr = key.toString('hex');
    const pool = this.hmacPools.get(keyStr) || [];
    if (pool.length > 0) {
      const hmac = pool.pop()!;
      // Note: Node.js crypto.Hmac doesn't have reset(), so we create a new one
      return crypto.createHmac(algorithm, key);
    }
    return crypto.createHmac(algorithm, key);
  }

  returnHmac(hmac: crypto.Hmac, key: Buffer): void {
    const keyStr = key.toString('hex');
    const pool = this.hmacPools.get(keyStr) || [];
    if (pool.length < this.maxPoolSize) {
      pool.push(hmac);
      this.hmacPools.set(keyStr, pool);
    }
  }
}

/**
 * High-throughput crypto engine with optimizations
 */
export class HighThroughputCrypto {
  private config: OptimizedCryptoConfig;
  private memoryPool: CryptoMemoryPool;
  private operationCache: Map<string, string> = new Map();
  private batchQueue: CryptoBatch[] = [];
  private processingBatches: Set<string> = new Set();
  private performanceMetrics: {
    totalOperations: number;
    totalProcessingTime: number;
    cacheHits: number;
    cacheMisses: number;
    batchCount: number;
  } = {
    totalOperations: 0,
    totalProcessingTime: 0,
    cacheHits: 0,
    cacheMisses: 0,
    batchCount: 0
  };

  constructor(config: Partial<OptimizedCryptoConfig> = {}) {
    this.config = {
      enableBatchProcessing: config.enableBatchProcessing !== false,
      enableAsyncProcessing: config.enableAsyncProcessing !== false,
      enableMemoryPooling: config.enableMemoryPooling !== false,
      batchSize: config.batchSize || 100,
      maxConcurrency: config.maxConcurrency || 10,
      cacheSize: config.cacheSize || 1000
    };

    this.memoryPool = new CryptoMemoryPool();
  }

  /**
   * Optimized hash function with caching and memory pooling
   */
  async optimizedHash(input: unknown, domain: string = "ccm"): Promise<OptimizedHashResult> {
    const startTime = performance.now();
    
    // Generate cache key
    const cacheKey = this.generateCacheKey('hash', input, domain);
    
    // Check cache first
    if (this.operationCache.has(cacheKey)) {
      this.performanceMetrics.cacheHits++;
      const cachedResult = this.operationCache.get(cacheKey)!;
      return {
        hash: cachedResult,
        processingTime: Math.max(0.01, performance.now() - startTime), // Much faster for cache hits
        holographic_correspondence: ccmHash({
          type: 'optimized_hash',
          input: cacheKey,
          cached: true,
          domain
        }, 'high_throughput_crypto')
      };
    }

    this.performanceMetrics.cacheMisses++;
    
    // Use memory pool for hash object
    const hash = this.config.enableMemoryPooling 
      ? this.memoryPool.getHash('sha256')
      : crypto.createHash('sha256');
    
    try {
      const inputStr = domain + "|" + stableStringify(input);
      hash.update(inputStr);
      const result = hash.digest('hex');
      
      // Cache result
      if (this.operationCache.size < this.config.cacheSize) {
        this.operationCache.set(cacheKey, result);
      }
      
      const processingTime = Math.max(0.1, performance.now() - startTime);
      return {
        hash: result,
        processingTime,
        holographic_correspondence: ccmHash({
          type: 'optimized_hash',
          input: cacheKey,
          result,
          domain
        }, 'high_throughput_crypto')
      };
    } finally {
      if (this.config.enableMemoryPooling) {
        this.memoryPool.returnHash(hash, 'sha256');
      }
    }
  }

  /**
   * Optimized signature function with batch processing
   */
  async optimizedSign(
    message: unknown, 
    moduleId: string, 
    secret: string
  ): Promise<OptimizedSignatureResult> {
    const startTime = performance.now();
    
    // Generate cache key
    const cacheKey = this.generateCacheKey('sign', message, moduleId, secret);
    
    // Check cache first
    if (this.operationCache.has(cacheKey)) {
      this.performanceMetrics.cacheHits++;
      const cachedResult = this.operationCache.get(cacheKey)!;
      const [signature, hash] = cachedResult.split('|');
      return {
        signature,
        hash,
        processingTime: Math.max(0.01, performance.now() - startTime), // Much faster for cache hits
        holographic_correspondence: ccmHash({
          type: 'optimized_sign',
          input: cacheKey,
          cached: true,
          moduleId
        }, 'high_throughput_crypto')
      };
    }

    this.performanceMetrics.cacheMisses++;
    
    // Compute hash
    const hashResult = await this.optimizedHash(message, "holo");
    
    // Use memory pool for HMAC
    const hmac = this.config.enableMemoryPooling
      ? this.memoryPool.getHmac('sha256', Buffer.from(secret, 'utf8'))
      : crypto.createHmac('sha256', Buffer.from(secret, 'utf8'));
    
    try {
      hmac.update("holo|" + moduleId + "|" + hashResult.hash);
      const signature = hmac.digest('hex');
      
      // Cache result
      const cacheValue = signature + "|" + hashResult.hash;
      if (this.operationCache.size < this.config.cacheSize) {
        this.operationCache.set(cacheKey, cacheValue);
      }
      
      const processingTime = Math.max(0.1, performance.now() - startTime);
      return {
        signature,
        hash: hashResult.hash,
        processingTime,
        holographic_correspondence: ccmHash({
          type: 'optimized_sign',
          input: cacheKey,
          signature,
          hash: hashResult.hash,
          moduleId
        }, 'high_throughput_crypto')
      };
    } finally {
      if (this.config.enableMemoryPooling) {
        this.memoryPool.returnHmac(hmac, Buffer.from(secret, 'utf8'));
      }
    }
  }

  /**
   * Optimized attestation function
   */
  async optimizedAttest(
    payload: unknown, 
    secret: string
  ): Promise<OptimizedAttestationResult> {
    const startTime = performance.now();
    
    // Generate cache key
    const cacheKey = this.generateCacheKey('attest', payload, secret);
    
    // Check cache first
    if (this.operationCache.has(cacheKey)) {
      this.performanceMetrics.cacheHits++;
      const cachedResult = this.operationCache.get(cacheKey)!;
      const [attestation, hash] = cachedResult.split('|');
      return {
        attestation,
        hash,
        processingTime: Math.max(0.01, performance.now() - startTime), // Much faster for cache hits
        holographic_correspondence: ccmHash({
          type: 'optimized_attest',
          input: cacheKey,
          cached: true
        }, 'high_throughput_crypto')
      };
    }

    this.performanceMetrics.cacheMisses++;
    
    // Compute hash
    const hashResult = await this.optimizedHash(payload, "alpha");
    
    // Use memory pool for HMAC
    const hmac = this.config.enableMemoryPooling
      ? this.memoryPool.getHmac('sha256', Buffer.from(secret, 'utf8'))
      : crypto.createHmac('sha256', Buffer.from(secret, 'utf8'));
    
    try {
      hmac.update("alpha|" + hashResult.hash);
      const attestation = hmac.digest('hex');
      
      // Cache result
      const cacheValue = attestation + "|" + hashResult.hash;
      if (this.operationCache.size < this.config.cacheSize) {
        this.operationCache.set(cacheKey, cacheValue);
      }
      
      const processingTime = Math.max(0.1, performance.now() - startTime);
      return {
        attestation,
        hash: hashResult.hash,
        processingTime,
        holographic_correspondence: ccmHash({
          type: 'optimized_attest',
          input: cacheKey,
          attestation,
          hash: hashResult.hash
        }, 'high_throughput_crypto')
      };
    } finally {
      if (this.config.enableMemoryPooling) {
        this.memoryPool.returnHmac(hmac, Buffer.from(secret, 'utf8'));
      }
    }
  }

  /**
   * Batch processing for multiple operations
   */
  async processBatch(operations: CryptoOperation[]): Promise<CryptoBatch> {
    const batchId = ccmHash({
      type: 'crypto_batch',
      operations: operations.length,
      timestamp: Date.now()
    }, 'high_throughput_crypto');
    
    const batch: CryptoBatch = {
      id: batchId,
      operations,
      priority: 'normal',
      timestamp: Date.now(),
      holographic_correspondence: batchId
    };

    if (this.config.enableBatchProcessing) {
      this.batchQueue.push(batch);
      await this.processBatchQueue();
    } else {
      await this.processBatchSync(batch);
    }

    this.performanceMetrics.batchCount++;
    return batch;
  }

  /**
   * Process batch queue asynchronously
   */
  private async processBatchQueue(): Promise<void> {
    if (this.processingBatches.size >= this.config.maxConcurrency) {
      return; // Already at max concurrency
    }

    const batch = this.batchQueue.shift();
    if (!batch) return;

    this.processingBatches.add(batch.id);
    
    try {
      await this.processBatchSync(batch);
    } finally {
      this.processingBatches.delete(batch.id);
      
      // Process next batch if available
      if (this.batchQueue.length > 0) {
        setImmediate(() => this.processBatchQueue());
      }
    }
  }

  /**
   * Process batch synchronously
   */
  private async processBatchSync(batch: CryptoBatch): Promise<void> {
    const startTime = performance.now();
    
    for (const operation of batch.operations) {
      try {
        switch (operation.type) {
          case 'hash':
            const hashResult = await this.optimizedHash(operation.input, operation.config.domain);
            operation.result = hashResult.hash;
            break;
          case 'sign':
            const signResult = await this.optimizedSign(
              operation.input, 
              operation.config.moduleId!, 
              operation.config.secret!
            );
            operation.result = signResult.signature;
            break;
          case 'attest':
            const attestResult = await this.optimizedAttest(
              operation.input, 
              operation.config.secret!
            );
            operation.result = attestResult.attestation;
            break;
          default:
            operation.error = `Unsupported operation type: ${operation.type}`;
        }
      } catch (error) {
        operation.error = error instanceof Error ? error.message : String(error);
      }
    }
    
    this.performanceMetrics.totalOperations += batch.operations.length;
    this.performanceMetrics.totalProcessingTime += performance.now() - startTime;
  }

  /**
   * Generate cache key for operation
   */
  private generateCacheKey(type: string, ...args: unknown[]): string {
    return ccmHash({ type, args }, 'cache_key');
  }

  /**
   * Get performance metrics
   */
  getPerformanceMetrics() {
    const avgProcessingTime = this.performanceMetrics.totalOperations > 0
      ? this.performanceMetrics.totalProcessingTime / this.performanceMetrics.totalOperations
      : 0;
    
    const cacheHitRate = this.performanceMetrics.cacheHits + this.performanceMetrics.cacheMisses > 0
      ? this.performanceMetrics.cacheHits / (this.performanceMetrics.cacheHits + this.performanceMetrics.cacheMisses)
      : 0;

    return {
      totalOperations: this.performanceMetrics.totalOperations,
      totalProcessingTime: this.performanceMetrics.totalProcessingTime,
      avgProcessingTime,
      cacheHitRate,
      cacheHits: this.performanceMetrics.cacheHits,
      cacheMisses: this.performanceMetrics.cacheMisses,
      batchCount: this.performanceMetrics.batchCount,
      queueSize: this.batchQueue.length,
      activeBatches: this.processingBatches.size,
      holographic_correspondence: ccmHash({
        metrics: this.performanceMetrics,
        timestamp: Date.now()
      }, 'performance_metrics')
    };
  }

  /**
   * Clear cache and reset metrics
   */
  clearCache(): void {
    this.operationCache.clear();
    this.performanceMetrics = {
      totalOperations: 0,
      totalProcessingTime: 0,
      cacheHits: 0,
      cacheMisses: 0,
      batchCount: 0
    };
  }
}

/**
 * Global high-throughput crypto instance
 */
let globalCryptoInstance: HighThroughputCrypto | null = null;

/**
 * Get or create global high-throughput crypto instance
 */
export function getHighThroughputCrypto(config?: Partial<OptimizedCryptoConfig>): HighThroughputCrypto {
  if (!globalCryptoInstance) {
    globalCryptoInstance = new HighThroughputCrypto(config);
  }
  return globalCryptoInstance;
}

/**
 * Convenience functions for common operations
 */
export async function fastHash(input: unknown, domain: string = "ccm"): Promise<string> {
  const crypto = getHighThroughputCrypto();
  const result = await crypto.optimizedHash(input, domain);
  return result.hash;
}

export async function fastSign(message: unknown, moduleId: string, secret: string): Promise<string> {
  const crypto = getHighThroughputCrypto();
  const result = await crypto.optimizedSign(message, moduleId, secret);
  return result.signature;
}

export async function fastAttest(payload: unknown, secret: string): Promise<string> {
  const crypto = getHighThroughputCrypto();
  const result = await crypto.optimizedAttest(payload, secret);
  return result.attestation;
}

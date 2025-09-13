/**
 * Parallel Processing Module
 * 
 * This module provides parallel processing capabilities for HoloPost operations,
 * allowing concurrent execution of transport, storage, and compute operations.
 */

import { createVerifier, createCTP, createStorage, spawnKernel } from '../adapters/hologram';
import { Budget, Witness, Receipt, CTPConfig, LatticeConfig, Postcard } from '../types';

/**
 * Configuration for parallel processing
 */
export interface ParallelConfig {
  maxConcurrency: number;
  timeout: number;
  retryAttempts: number;
  retryDelay: number;
}

/**
 * Default parallel processing configuration
 */
const DEFAULT_CONFIG: ParallelConfig = {
  maxConcurrency: 4,
  timeout: 30000,
  retryAttempts: 3,
  retryDelay: 1000,
};

/**
 * Result of a parallel operation
 */
export interface ParallelResult<T> {
  success: boolean;
  data?: T;
  error?: Error;
  duration: number;
  retries: number;
}

/**
 * Parallel operation context
 */
interface ParallelContext {
  config: ParallelConfig;
  verifier: any;
  ctp?: any;
  storage?: any;
}

/**
 * Create a parallel processor with the given configuration
 */
export class ParallelProcessor {
  private config: ParallelConfig;
  private context: ParallelContext;

  constructor(config: Partial<ParallelConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
    this.context = {
      config: this.config,
      verifier: null,
    };
  }

  /**
   * Initialize the parallel processor
   */
  async initialize(): Promise<void> {
    console.log('🚀 Initializing parallel processor...');
    this.context.verifier = await createVerifier();
    console.log('✅ Parallel processor initialized');
  }

  /**
   * Execute multiple transport operations in parallel
   */
  async parallelTransport(
    operations: Array<{
      lane: number;
      payload: Buffer;
      budget: Budget;
      attach: { r96: string; probes: number };
    }>,
    ctpConfig: CTPConfig
  ): Promise<ParallelResult<any>[]> {
    console.log(`📤 Starting parallel transport for ${operations.length} operations`);
    
    if (!this.context.ctp) {
      this.context.ctp = await createCTP(ctpConfig);
    }

    const results = await this.executeParallel(
      operations,
      async (op) => {
        const startTime = Date.now();
        try {
          const result = await this.context.ctp.send(op);
          return {
            success: true,
            data: result,
            duration: Date.now() - startTime,
            retries: 0,
          };
        } catch (error) {
          return {
            success: false,
            error: error as Error,
            duration: Date.now() - startTime,
            retries: 0,
          };
        }
      }
    );

    console.log(`✅ Parallel transport completed: ${results.filter(r => r.success).length}/${results.length} successful`);
    return results;
  }

  /**
   * Execute multiple storage operations in parallel
   */
  async parallelStorage(
    operations: Array<{
      id: string;
      bytes: Buffer;
      policy: any;
      budget: Budget;
      witness: Witness;
    }>,
    latticeConfig: LatticeConfig
  ): Promise<ParallelResult<Receipt>[]> {
    console.log(`💾 Starting parallel storage for ${operations.length} operations`);
    
    if (!this.context.storage) {
      this.context.storage = await createStorage(latticeConfig);
    }

    const results = await this.executeParallel(
      operations,
      async (op) => {
        const startTime = Date.now();
        try {
          const result = await this.context.storage.put(op);
          return {
            success: true,
            data: result,
            duration: Date.now() - startTime,
            retries: 0,
          };
        } catch (error) {
          return {
            success: false,
            error: error as Error,
            duration: Date.now() - startTime,
            retries: 0,
          };
        }
      }
    );

    console.log(`✅ Parallel storage completed: ${results.filter(r => r.success).length}/${results.length} successful`);
    return results;
  }

  /**
   * Execute multiple compute operations in parallel
   */
  async parallelCompute(
    operations: Array<{
      name: string;
      inputs: Array<{ id: string }>;
      budget: Budget;
      pin?: { near?: string; lane?: number };
    }>,
    latticeConfig: LatticeConfig
  ): Promise<ParallelResult<any>[]> {
    console.log(`⚙️  Starting parallel compute for ${operations.length} operations`);
    
    if (!this.context.storage) {
      this.context.storage = await createStorage(latticeConfig);
    }

    const results = await this.executeParallel(
      operations,
      async (op) => {
        const startTime = Date.now();
        try {
          const kernel = await spawnKernel({
            name: op.name,
            inputs: op.inputs,
            budget: op.budget,
            ...(op.pin && { pin: op.pin }),
          });
          
          const result = await kernel.await();
          return {
            success: true,
            data: result,
            duration: Date.now() - startTime,
            retries: 0,
          };
        } catch (error) {
          return {
            success: false,
            error: error as Error,
            duration: Date.now() - startTime,
            retries: 0,
          };
        }
      }
    );

    console.log(`✅ Parallel compute completed: ${results.filter(r => r.success).length}/${results.length} successful`);
    return results;
  }

  /**
   * Execute multiple postcard operations in parallel
   */
  async parallelPostcards(
    postcards: Postcard[],
    latticeConfig: LatticeConfig
  ): Promise<ParallelResult<any>[]> {
    console.log(`📮 Starting parallel postcard processing for ${postcards.length} postcards`);
    
    if (!this.context.storage) {
      this.context.storage = await createStorage(latticeConfig);
    }

    const results = await this.executeParallel(
      postcards,
      async (postcard) => {
        const startTime = Date.now();
        try {
          // Store postcard
          const witness: Witness = {
            r96: this.context.verifier.r96(postcard.bytes),
            probes: 192,
            timestamp: Date.now(),
          };

          const receipt = await this.context.storage.put({
            id: postcard.id,
            bytes: postcard.bytes,
            policy: {},
            budget: { io: 100, cpuMs: 50 },
            witness,
          });

          return {
            success: true,
            data: { postcard, receipt },
            duration: Date.now() - startTime,
            retries: 0,
          };
        } catch (error) {
          return {
            success: false,
            error: error as Error,
            duration: Date.now() - startTime,
            retries: 0,
          };
        }
      }
    );

    console.log(`✅ Parallel postcard processing completed: ${results.filter(r => r.success).length}/${results.length} successful`);
    return results;
  }

  /**
   * Execute operations in parallel with concurrency control
   */
  private async executeParallel<T, R>(
    operations: T[],
    processor: (operation: T) => Promise<ParallelResult<R>>
  ): Promise<ParallelResult<R>[]> {
    const results: ParallelResult<R>[] = [];
    const chunks = this.chunkArray(operations, this.config.maxConcurrency);

    for (const chunk of chunks) {
      const chunkPromises = chunk.map(operation => 
        this.executeWithRetry(operation, processor)
      );
      
      const chunkResults = await Promise.all(chunkPromises);
      results.push(...chunkResults);
    }

    return results;
  }

  /**
   * Execute an operation with retry logic
   */
  private async executeWithRetry<T, R>(
    operation: T,
    processor: (operation: T) => Promise<ParallelResult<R>>,
    attempt: number = 1
  ): Promise<ParallelResult<R>> {
    try {
      const result = await processor(operation);
      
      if (!result.success && attempt < this.config.retryAttempts) {
        console.log(`🔄 Retrying operation (attempt ${attempt + 1}/${this.config.retryAttempts})`);
        await this.delay(this.config.retryDelay * attempt);
        return this.executeWithRetry(operation, processor, attempt + 1);
      }
      
      return { ...result, retries: attempt - 1 };
    } catch (error) {
      if (attempt < this.config.retryAttempts) {
        console.log(`🔄 Retrying operation after error (attempt ${attempt + 1}/${this.config.retryAttempts}):`, error);
        await this.delay(this.config.retryDelay * attempt);
        return this.executeWithRetry(operation, processor, attempt + 1);
      }
      
      return {
        success: false,
        error: error as Error,
        duration: 0,
        retries: attempt - 1,
      };
    }
  }

  /**
   * Split array into chunks of specified size
   */
  private chunkArray<T>(array: T[], chunkSize: number): T[][] {
    const chunks: T[][] = [];
    for (let i = 0; i < array.length; i += chunkSize) {
      chunks.push(array.slice(i, i + chunkSize));
    }
    return chunks;
  }

  /**
   * Delay execution for specified milliseconds
   */
  private delay(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  /**
   * Get performance statistics
   */
  getStats(results: ParallelResult<any>[]): {
    total: number;
    successful: number;
    failed: number;
    averageDuration: number;
    totalDuration: number;
    totalRetries: number;
  } {
    const successful = results.filter(r => r.success);
    const failed = results.filter(r => !r.success);
    const totalDuration = results.reduce((sum, r) => sum + r.duration, 0);
    const totalRetries = results.reduce((sum, r) => sum + r.retries, 0);

    return {
      total: results.length,
      successful: successful.length,
      failed: failed.length,
      averageDuration: results.length > 0 ? totalDuration / results.length : 0,
      totalDuration,
      totalRetries,
    };
  }

  /**
   * Clean up resources
   */
  async cleanup(): Promise<void> {
    console.log('🧹 Cleaning up parallel processor...');
    
    if (this.context.ctp) {
      await this.context.ctp.close();
    }
    
    console.log('✅ Parallel processor cleaned up');
  }
}

/**
 * Utility function to create a parallel processor with default configuration
 */
export function createParallelProcessor(config?: Partial<ParallelConfig>): ParallelProcessor {
  return new ParallelProcessor(config);
}

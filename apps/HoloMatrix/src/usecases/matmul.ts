/**
 * Matrix Multiplication Use Case
 * Generates and manages matrices A, B for block-based matrix multiplication
 * Provides iterators for streaming matrix blocks over the hologram network
 */

import type { Budget, Witness, MatMulConfig } from '../types';
import { uorIdFromBytes, mkWitness } from '../testkit';
import { generateR96 } from '../utils/r96';

export interface MatrixBlock {
  id: string;
  bytes: Buffer;
  row: number;  // block row index
  col: number;  // block col index
  size: number;
  matrixId: 'A' | 'B' | 'C';
  uorId: string;
  witness: Witness;
}

export interface MatrixIterator {
  next(): IteratorResult<MatrixBlock>;
  [Symbol.iterator](): Iterator<MatrixBlock>;
  reset(): void;
  getProgress(): { current: number; total: number; percentage: number };
}

export class MatrixMultiplicationUseCase {
  private config: MatMulConfig;
  private matrixA: Int16Array;
  private matrixB: Int16Array;
  // private matrixC: Int16Array; // Unused for now
  private blocks: MatrixBlock[] = [];
  private enableLogging: boolean = true;

  constructor(config: MatMulConfig, enableLogging: boolean = true) {
    this.config = config;
    this.matrixA = new Int16Array(config.size * config.size);
    this.matrixB = new Int16Array(config.size * config.size);
    // this.matrixC = new Int16Array(config.size * config.size); // Unused for now
    this.enableLogging = enableLogging;
    
    // Note: initializeMatrices() and generateBlocks() will be called separately
    // to allow for async initialization
  }

  /**
   * Initialize the use case (call this after constructor)
   */
  async initialize(): Promise<void> {
    await this.initializeMatrices();
    this.generateBlocks();
  }

  /**
   * Initialize matrices A and B with test data (optimized for large matrices)
   */
  private async initializeMatrices(): Promise<void> {
    console.log(`Initializing matrices A and B (${this.config.size}×${this.config.size})`);
    
    const totalElements = this.config.size * this.config.size;
    const batchSize = Math.min(1024 * 1024, totalElements); // Process in 1M element batches
    const totalBatches = Math.ceil(totalElements / batchSize);
    
    console.log(`Processing ${totalElements.toLocaleString()} elements in ${totalBatches} batches of ${batchSize.toLocaleString()}`);
    
    // Initialize matrix A with deterministic values (async with progress)
    for (let batch = 0; batch < totalBatches; batch++) {
      const startIdx = batch * batchSize;
      const endIdx = Math.min(startIdx + batchSize, totalElements);
      
      for (let idx = startIdx; idx < endIdx; idx++) {
        const i = Math.floor(idx / this.config.size);
        const j = idx % this.config.size;
        this.matrixA[idx] = (i + j) % 100; // Deterministic pattern
      }
      
      // Yield control every batch to prevent blocking
      if (batch % 10 === 0) {
        console.log(`  Matrix A: ${((batch + 1) / totalBatches * 100).toFixed(1)}% complete`);
        await new Promise(resolve => setImmediate(resolve));
      }
    }

    // Initialize matrix B with deterministic values (async with progress)
    for (let batch = 0; batch < totalBatches; batch++) {
      const startIdx = batch * batchSize;
      const endIdx = Math.min(startIdx + batchSize, totalElements);
      
      for (let idx = startIdx; idx < endIdx; idx++) {
        const i = Math.floor(idx / this.config.size);
        const j = idx % this.config.size;
        this.matrixB[idx] = (i * j) % 100; // Different deterministic pattern
      }
      
      // Yield control every batch to prevent blocking
      if (batch % 10 === 0) {
        if (this.enableLogging) {
          console.log(`  Matrix B: ${((batch + 1) / totalBatches * 100).toFixed(1)}% complete`);
        }
        await new Promise(resolve => setImmediate(resolve));
      }
    }

    if (this.enableLogging) {
      console.log(`Matrices initialized with ${totalElements.toLocaleString()} elements each`);
    }
  }

  /**
   * Generate all matrix blocks
   */
  private generateBlocks(): void {
    const blockCount = Math.ceil(this.config.size / this.config.block);
    if (this.enableLogging) {
      console.log(`Generating ${blockCount}×${blockCount} blocks of size ${this.config.block}×${this.config.block}`);
    }

    // Generate blocks for matrix A
    for (let blockRow = 0; blockRow < blockCount; blockRow++) {
      for (let blockCol = 0; blockCol < blockCount; blockCol++) {
        const block = this.createMatrixBlock('A', blockRow, blockCol);
        this.blocks.push(block);
      }
    }

    // Generate blocks for matrix B
    for (let blockRow = 0; blockRow < blockCount; blockRow++) {
      for (let blockCol = 0; blockCol < blockCount; blockCol++) {
        const block = this.createMatrixBlock('B', blockRow, blockCol);
        this.blocks.push(block);
      }
    }

    if (this.enableLogging) {
      console.log(`Generated ${this.blocks.length} total blocks`);
    }
  }

  /**
   * Create a matrix block
   */
  private createMatrixBlock(matrixId: 'A' | 'B', blockRow: number, blockCol: number): MatrixBlock {
    const blockSize = this.config.block;
    const blockData = new Int16Array(blockSize * blockSize);
    
    // Extract block data from the appropriate matrix
    const sourceMatrix = matrixId === 'A' ? this.matrixA : this.matrixB;
    
    for (let i = 0; i < blockSize; i++) {
      for (let j = 0; j < blockSize; j++) {
        const sourceRow = blockRow * blockSize + i;
        const sourceCol = blockCol * blockSize + j;
        
        if (sourceRow < this.config.size && sourceCol < this.config.size) {
          const sourceIndex = sourceRow * this.config.size + sourceCol;
          const blockIndex = i * blockSize + j;
          blockData[blockIndex] = sourceMatrix[sourceIndex] || 0;
        } else {
          // Pad with zeros for incomplete blocks
          const blockIndex = i * blockSize + j;
          blockData[blockIndex] = 0;
        }
      }
    }

    // Serialize block data
    const bytes = Buffer.from(blockData.buffer);
    
    // Generate UOR ID
    const uorId = uorIdFromBytes(bytes);
    
    // Create witness
    const witness = mkWitness(this.generateR96(bytes));

    return {
      id: `${matrixId}-block-${blockRow}-${blockCol}`,
      bytes,
      row: blockRow,
      col: blockCol,
      size: blockSize,
      matrixId,
      uorId,
      witness
    };
  }

  /**
   * Generate R96 hash for buffer
   */
  private generateR96(buffer: Buffer): string {
    // Use centralized R96 generation to match SDK
    return generateR96(buffer);
  }

  /**
   * Create iterator for matrix A blocks
   */
  createMatrixAIterator(): MatrixIterator {
    const matrixABlocks = this.blocks.filter(block => block.matrixId === 'A');
    return new MatrixBlockIterator(matrixABlocks);
  }

  /**
   * Create iterator for matrix B blocks
   */
  createMatrixBIterator(): MatrixIterator {
    const matrixBBlocks = this.blocks.filter(block => block.matrixId === 'B');
    return new MatrixBlockIterator(matrixBBlocks);
  }

  /**
   * Create iterator for all blocks
   */
  createAllBlocksIterator(): MatrixIterator {
    return new MatrixBlockIterator([...this.blocks]);
  }

  /**
   * Get block by ID
   */
  getBlock(id: string): MatrixBlock | undefined {
    return this.blocks.find(block => block.id === id);
  }

  /**
   * Get blocks by matrix ID
   */
  getBlocksByMatrix(matrixId: 'A' | 'B'): MatrixBlock[] {
    return this.blocks.filter(block => block.matrixId === matrixId);
  }

  /**
   * Get all blocks
   */
  getAllBlocks(): MatrixBlock[] {
    return [...this.blocks];
  }

  /**
   * Create output block for matrix C
   */
  createOutputBlock(blockRow: number, blockCol: number): MatrixBlock {
    const blockSize = this.config.block;
    const blockData = new Int16Array(blockSize * blockSize);
    
    // Initialize with zeros
    blockData.fill(0);
    
    const bytes = Buffer.from(blockData.buffer);
    const uorId = uorIdFromBytes(bytes);
    const witness = mkWitness(this.generateR96(bytes));

    return {
      id: `C-block-${blockRow}-${blockCol}`,
      bytes,
      row: blockRow,
      col: blockCol,
      size: blockSize,
      matrixId: 'C',
      uorId,
      witness
    };
  }

  /**
   * Perform block matrix multiplication (test implementation)
   */
  multiplyBlocks(blockA: MatrixBlock, blockB: MatrixBlock): MatrixBlock {
    const blockSize = this.config.block;
    const resultData = new Int16Array(blockSize * blockSize);
    
    // Extract data from blocks
    const dataA = new Int16Array(blockA.bytes.buffer);
    const dataB = new Int16Array(blockB.bytes.buffer);
    
    // Perform matrix multiplication
    for (let i = 0; i < blockSize; i++) {
      for (let j = 0; j < blockSize; j++) {
        let sum = 0;
        for (let k = 0; k < blockSize; k++) {
          sum += (dataA[i * blockSize + k] || 0) * (dataB[k * blockSize + j] || 0);
        }
        resultData[i * blockSize + j] = sum;
      }
    }
    
    const bytes = Buffer.from(resultData.buffer);
    const uorId = uorIdFromBytes(bytes);
    const witness = mkWitness(this.generateR96(bytes));

    return {
      id: `result-${blockA.id}-${blockB.id}`,
      bytes,
      row: blockA.row,
      col: blockB.col,
      size: blockSize,
      matrixId: 'C',
      uorId,
      witness
    };
  }

  /**
   * Create budget for matrix operations
   */
  createBudget(operation: 'transport' | 'storage' | 'compute'): Budget {
    switch (operation) {
      case 'transport':
        return { cpuMs: 5, io: 1, mem: 4096 };
      case 'storage':
        return { cpuMs: 10, io: 2, mem: 8192 };
      case 'compute':
        return { cpuMs: 50, io: 1, mem: 16384 };
      default:
        return { cpuMs: 10, io: 1, mem: 4096 };
    }
  }

  /**
   * Get matrix statistics
   */
  getStats(): {
    matrixSize: number;
    blockSize: number;
    totalBlocks: number;
    blocksPerMatrix: number;
    totalDataSize: number;
    averageBlockSize: number;
  } {
    const totalBlocks = this.blocks.length;
    const blocksPerMatrix = totalBlocks / 2; // A and B matrices
    const totalDataSize = this.blocks.reduce((sum, block) => sum + block.bytes.length, 0);
    const averageBlockSize = totalBlocks > 0 ? totalDataSize / totalBlocks : 0;

    return {
      matrixSize: this.config.size,
      blockSize: this.config.block,
      totalBlocks,
      blocksPerMatrix,
      totalDataSize,
      averageBlockSize
    };
  }

  /**
   * Validate block structure
   */
  validateBlock(block: MatrixBlock): boolean {
    return !!(
      block.id &&
      block.bytes &&
      typeof block.row === 'number' &&
      typeof block.col === 'number' &&
      typeof block.size === 'number' &&
      ['A', 'B', 'C'].includes(block.matrixId) &&
      block.uorId &&
      block.witness &&
      block.bytes.length === block.size * block.size * 2 // Int16 = 2 bytes
    );
  }
}

class MatrixBlockIterator implements MatrixIterator {
  private blocks: MatrixBlock[];
  private currentIndex: number = 0;

  constructor(blocks: MatrixBlock[]) {
    this.blocks = blocks;
  }

  next(): IteratorResult<MatrixBlock> {
    if (this.currentIndex >= this.blocks.length) {
      return { done: true, value: undefined };
    }

    const block = this.blocks[this.currentIndex];
    this.currentIndex++;
    
    return { done: false, value: block! };
  }

  [Symbol.iterator](): Iterator<MatrixBlock> {
    return this;
  }

  reset(): void {
    this.currentIndex = 0;
  }

  getProgress(): { current: number; total: number; percentage: number } {
    const current = this.currentIndex;
    const total = this.blocks.length;
    const percentage = total > 0 ? (current / total) * 100 : 0;
    
    return { current, total, percentage };
  }
}

/**
 * Create a matrix multiplication use case instance
 */
export async function createMatMulUseCase(config: MatMulConfig, enableLogging: boolean = true): Promise<MatrixMultiplicationUseCase> {
  const useCase = new MatrixMultiplicationUseCase(config, enableLogging);
  await useCase.initialize();
  return useCase;
}

/**
 * Create default matrix multiplication configuration
 */
export function createDefaultMatMulConfig(): MatMulConfig {
  return {
    size: 2048,
    block: 128,
    lanes: 64,
    payload: 8192,  // Increased from 4096 to 8192 for better throughput
    batch: 256,     // Increased from 16 to 256 for better batching
    workers: 8,     // Increased from 4 to 8 for more parallelism
    window: 100,
    targetGbps: 1.0, // More realistic target for initial testing
    iterations: 200  // Default iterations for sustained throughput
  };
}

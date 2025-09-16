/**
 * Tests for Matrix Multiplication Use Case
 */

import { createMatMulUseCase, createDefaultMatMulConfig } from './matmul';
import type { MatMulConfig } from '../types';

describe('MatrixMultiplicationUseCase', () => {
  let useCase: any;
  let config: MatMulConfig;

  beforeEach(async () => {
    config = {
      size: 64, // Small size for testing
      block: 16,
      lanes: 8,
      payload: 1024,
      batch: 4,
      workers: 2,
      window: 50,
      targetGbps: 10
    };
    useCase = await createMatMulUseCase(config, false); // Disable logging for tests
  });

  describe('matrix initialization', () => {
    it('should initialize matrices with correct size', () => {
      const stats = useCase.getStats();
      
      expect(stats.matrixSize).toBe(64);
      expect(stats.blockSize).toBe(16);
      expect(stats.totalBlocks).toBe(32); // 4x4 blocks for each matrix (A and B)
      expect(stats.blocksPerMatrix).toBe(16); // 4x4 blocks per matrix
    });

    it('should generate deterministic matrix data', () => {
      const blockA1 = useCase.getBlock('A-block-0-0');
      const blockA2 = useCase.getBlock('A-block-0-0');
      
      expect(blockA1).toBeDefined();
      expect(blockA2).toBeDefined();
      expect(blockA1.bytes).toEqual(blockA2.bytes);
    });
  });

  describe('block generation', () => {
    it('should create valid matrix blocks', () => {
      const block = useCase.getBlock('A-block-0-0');
      
      expect(block).toBeDefined();
      expect(block.id).toBe('A-block-0-0');
      expect(block.matrixId).toBe('A');
      expect(block.row).toBe(0);
      expect(block.col).toBe(0);
      expect(block.size).toBe(16);
      expect(block.bytes).toBeInstanceOf(Buffer);
      expect(block.uorId).toMatch(/^uor:[a-f0-9]{24}$/);
      expect(block.witness).toBeDefined();
    });

    it('should validate block structure', () => {
      const block = useCase.getBlock('A-block-0-0');
      
      expect(useCase.validateBlock(block)).toBe(true);
    });

    it('should reject invalid block structure', () => {
      const invalidBlock = {
        id: 'invalid',
        bytes: Buffer.alloc(100),
        row: 'invalid',
        col: 0,
        size: 16,
        matrixId: 'A',
        uorId: 'invalid',
        witness: {}
      };
      
      expect(useCase.validateBlock(invalidBlock)).toBe(false);
    });
  });

  describe('iterators', () => {
    it('should create matrix A iterator', () => {
      const iterator = useCase.createMatrixAIterator();
      const blocks: any[] = [];
      
      for (const block of iterator) {
        blocks.push(block);
      }
      
      expect(blocks).toHaveLength(16); // 4x4 blocks
      expect(blocks.every(block => block.matrixId === 'A')).toBe(true);
    });

    it('should create matrix B iterator', () => {
      const iterator = useCase.createMatrixBIterator();
      const blocks: any[] = [];
      
      for (const block of iterator) {
        blocks.push(block);
      }
      
      expect(blocks).toHaveLength(16); // 4x4 blocks
      expect(blocks.every(block => block.matrixId === 'B')).toBe(true);
    });

    it('should create all blocks iterator', () => {
      const iterator = useCase.createAllBlocksIterator();
      const blocks: any[] = [];
      
      for (const block of iterator) {
        blocks.push(block);
      }
      
      expect(blocks).toHaveLength(32); // 16 blocks for A + 16 blocks for B
    });

    it('should track iterator progress', () => {
      const iterator = useCase.createMatrixAIterator();
      
      // Initial progress
      let progress = iterator.getProgress();
      expect(progress.current).toBe(0);
      expect(progress.total).toBe(16);
      expect(progress.percentage).toBe(0);
      
      // After consuming some blocks
      iterator.next();
      iterator.next();
      
      progress = iterator.getProgress();
      expect(progress.current).toBe(2);
      expect(progress.percentage).toBe(12.5);
    });

    it('should reset iterator', () => {
      const iterator = useCase.createMatrixAIterator();
      
      // Consume some blocks
      iterator.next();
      iterator.next();
      
      // Reset
      iterator.reset();
      
      const progress = iterator.getProgress();
      expect(progress.current).toBe(0);
      expect(progress.percentage).toBe(0);
    });
  });

  describe('block operations', () => {
    it('should get blocks by matrix ID', () => {
      const matrixABlocks = useCase.getBlocksByMatrix('A');
      const matrixBBlocks = useCase.getBlocksByMatrix('B');
      
      expect(matrixABlocks).toHaveLength(16);
      expect(matrixBBlocks).toHaveLength(16);
      expect(matrixABlocks.every((block: any) => block.matrixId === 'A')).toBe(true);
      expect(matrixBBlocks.every((block: any) => block.matrixId === 'B')).toBe(true);
    });

    it('should create output blocks', () => {
      const outputBlock = useCase.createOutputBlock(0, 0);
      
      expect(outputBlock).toBeDefined();
      expect(outputBlock.id).toBe('C-block-0-0');
      expect(outputBlock.matrixId).toBe('C');
      expect(outputBlock.row).toBe(0);
      expect(outputBlock.col).toBe(0);
      expect(outputBlock.size).toBe(16);
      expect(outputBlock.bytes).toBeInstanceOf(Buffer);
    });

    it('should multiply blocks', () => {
      const blockA = useCase.getBlock('A-block-0-0');
      const blockB = useCase.getBlock('B-block-0-0');
      
      const result = useCase.multiplyBlocks(blockA, blockB);
      
      expect(result).toBeDefined();
      expect(result.id).toBe('result-A-block-0-0-B-block-0-0');
      expect(result.matrixId).toBe('C');
      expect(result.row).toBe(0);
      expect(result.col).toBe(0);
      expect(result.size).toBe(16);
      expect(result.bytes).toBeInstanceOf(Buffer);
    });
  });

  describe('budget creation', () => {
    it('should create transport budget', () => {
      const budget = useCase.createBudget('transport');
      
      expect(budget.cpuMs).toBe(5);
      expect(budget.io).toBe(1);
      expect(budget.mem).toBe(4096);
    });

    it('should create storage budget', () => {
      const budget = useCase.createBudget('storage');
      
      expect(budget.cpuMs).toBe(10);
      expect(budget.io).toBe(2);
      expect(budget.mem).toBe(8192);
    });

    it('should create compute budget', () => {
      const budget = useCase.createBudget('compute');
      
      expect(budget.cpuMs).toBe(50);
      expect(budget.io).toBe(1);
      expect(budget.mem).toBe(16384);
    });

    it('should create default budget', () => {
      const budget = useCase.createBudget('unknown');
      
      expect(budget.cpuMs).toBe(10);
      expect(budget.io).toBe(1);
      expect(budget.mem).toBe(4096);
    });
  });

  describe('statistics', () => {
    it('should provide correct statistics', () => {
      const stats = useCase.getStats();
      
      expect(stats.matrixSize).toBe(64);
      expect(stats.blockSize).toBe(16);
      expect(stats.totalBlocks).toBe(32);
      expect(stats.blocksPerMatrix).toBe(16);
      expect(stats.totalDataSize).toBeGreaterThan(0);
      expect(stats.averageBlockSize).toBeGreaterThan(0);
    });
  });
});

describe('createDefaultMatMulConfig', () => {
  it('should create default configuration', () => {
    const config = createDefaultMatMulConfig();
    
    expect(config.size).toBe(2048);
    expect(config.block).toBe(128);
    expect(config.lanes).toBe(64);
    expect(config.payload).toBe(8192);
    expect(config.batch).toBe(256);
    expect(config.workers).toBe(8);
    expect(config.window).toBe(100);
    expect(config.targetGbps).toBe(1.0);
  });
});

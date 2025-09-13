/**
 * Unit tests for Verifier functionality
 */

import { createVerifier } from '../src/adapters/hologram';
import { Budget } from '../src/types';

describe('Verifier', () => {
  let verifier: any;

  beforeEach(async () => {
    verifier = await createVerifier();
  });

  describe('r96 checksum', () => {
    it('should return deterministic strings for the same bytes', () => {
      const bytes1 = Buffer.from('Hello, World!', 'utf8');
      const bytes2 = Buffer.from('Hello, World!', 'utf8');
      
      const r96_1 = verifier.r96(bytes1);
      const r96_2 = verifier.r96(bytes2);
      
      expect(r96_1).toBe(r96_2);
      expect(r96_1).toHaveLength(24);
      expect(r96_1).toMatch(/^[0-9a-f]+$/);
    });

    it('should return different strings for different bytes', () => {
      const bytes1 = Buffer.from('Hello, World!', 'utf8');
      const bytes2 = Buffer.from('Hello, Universe!', 'utf8');
      
      const r96_1 = verifier.r96(bytes1);
      const r96_2 = verifier.r96(bytes2);
      
      expect(r96_1).not.toBe(r96_2);
    });

    it('should handle empty buffers', () => {
      const emptyBuffer = Buffer.alloc(0);
      const r96 = verifier.r96(emptyBuffer);
      
      expect(r96).toHaveLength(24);
      expect(r96).toMatch(/^[0-9a-f]+$/);
    });

    it('should handle large buffers', () => {
      const largeBuffer = Buffer.alloc(1024 * 1024, 'A'); // 1MB buffer
      const r96 = verifier.r96(largeBuffer);
      
      expect(r96).toHaveLength(24);
      expect(r96).toMatch(/^[0-9a-f]+$/);
    });
  });

  describe('klein probe', () => {
    it('should return boolean values', () => {
      const frame1 = Buffer.from('test frame 1', 'utf8');
      const frame2 = Buffer.from('test frame 2', 'utf8');
      
      const result1 = verifier.klein(frame1);
      const result2 = verifier.klein(frame2);
      
      expect(typeof result1).toBe('boolean');
      expect(typeof result2).toBe('boolean');
    });

    it('should return true for non-empty frames', () => {
      const frame = Buffer.from('test frame', 'utf8');
      const result = verifier.klein(frame);
      
      expect(result).toBe(true);
    });

    it('should return false for empty frames', () => {
      const emptyFrame = Buffer.alloc(0);
      const result = verifier.klein(emptyFrame);
      
      expect(result).toBe(false);
    });
  });

  describe('budget math', () => {
    it('should add budgets correctly', () => {
      const budget1: Budget = { io: 100, cpuMs: 50, mem: 32 };
      const budget2: Budget = { io: 200, cpuMs: 75, mem: 64 };
      
      const result = verifier.budget.add(budget1, budget2);
      
      expect(result.io).toBe(300);
      expect(result.cpuMs).toBe(125);
      expect(result.mem).toBe(96);
    });

    it('should subtract budgets correctly', () => {
      const budget1: Budget = { io: 300, cpuMs: 125, mem: 96 };
      const budget2: Budget = { io: 100, cpuMs: 50, mem: 32 };
      
      const result = verifier.budget.sub(budget1, budget2);
      
      expect(result.io).toBe(200);
      expect(result.cpuMs).toBe(75);
      expect(result.mem).toBe(64);
    });

    it('should not allow negative budget values', () => {
      const budget1: Budget = { io: 100, cpuMs: 50, mem: 32 };
      const budget2: Budget = { io: 200, cpuMs: 75, mem: 64 };
      
      const result = verifier.budget.sub(budget1, budget2);
      
      expect(result.io).toBe(0);
      expect(result.cpuMs).toBe(0);
      expect(result.mem).toBe(0);
    });

    it('should create zero budget', () => {
      const zeroBudget = verifier.budget.zero();
      
      expect(zeroBudget.io).toBe(0);
      expect(zeroBudget.cpuMs).toBe(0);
      expect(zeroBudget.mem).toBe(0);
    });

    it('should detect zero budgets', () => {
      const zeroBudget: Budget = { io: 0, cpuMs: 0, mem: 0 };
      const nonZeroBudget: Budget = { io: 100, cpuMs: 50, mem: 32 };
      
      expect(verifier.budget.isZero(zeroBudget)).toBe(true);
      expect(verifier.budget.isZero(nonZeroBudget)).toBe(false);
    });

    it('should handle budgets with undefined mem', () => {
      const budget1: Budget = { io: 100, cpuMs: 50 };
      const budget2: Budget = { io: 200, cpuMs: 75, mem: 32 };
      
      const result = verifier.budget.add(budget1, budget2);
      
      expect(result.io).toBe(300);
      expect(result.cpuMs).toBe(125);
      expect(result.mem).toBe(32);
    });
  });
});

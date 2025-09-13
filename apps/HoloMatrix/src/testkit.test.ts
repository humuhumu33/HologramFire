/**
 * Tests for Testkit utilities
 */

import {
  budget,
  zeroBudget,
  assertClosed,
  mkWitness,
  uorIdFromBytes,
  place,
  validateCoords,
  mkMatrixBlock,
  measureTime,
  mkTransportFrame,
  validateBudget,
  hasBudget,
  mkStoragePolicy,
  mkTestData,
  mkComputeKernel,
  sleep,
  mkNodeId,
  validateReceipt,
  mkAdapter
} from './testkit';
import type { Receipt } from './types';
import { GATES } from './types';

describe('Testkit', () => {
  describe('budget', () => {
    it('should create budget with default values', () => {
      const b = budget();
      expect(b).toBeValidBudget();
      expect(b.cpuMs).toBe(1000);
      expect(b.io).toBe(1000);
      expect(b.mem).toBe(1000);
    });

    it('should create budget with custom values', () => {
      const b = budget(500, 200, 2048);
      expect(b).toBeValidBudget();
      expect(b.cpuMs).toBe(500);
      expect(b.io).toBe(200);
      expect(b.mem).toBe(2048);
    });
  });

  describe('zeroBudget', () => {
    it('should create zero budget', () => {
      const b = zeroBudget();
      expect(b).toBeValidBudget();
      expect(b.cpuMs).toBe(0);
      expect(b.io).toBe(0);
      expect(b.mem).toBe(0);
    });
  });

  describe('assertClosed', () => {
    it('should pass for closed receipt', () => {
      const receipt = {
        ok: true,
        windowClosed: true,
        budgetAfter: { io: 0, cpuMs: 0, mem: 0 },
        details: { gate: GATES.RECEIPT }
      };
      
      expect(() => assertClosed(receipt)).not.toThrow();
    });

    it('should pass for closed receipt with correct gate', () => {
      const receipt = {
        ok: true,
        windowClosed: true,
        budgetAfter: { io: 0, cpuMs: 0, mem: 0 },
        details: { gate: GATES.RECEIPT }
      };
      
      expect(() => assertClosed(receipt, GATES.RECEIPT)).not.toThrow();
    });

    it('should throw for unclosed receipt', () => {
      const receipt: Receipt = {
        ok: true,
        windowClosed: false,
        budgetAfter: { io: 0, cpuMs: 0, mem: 0 },
        details: { gate: GATES.RECEIPT }
      };
      
      expect(() => assertClosed(receipt)).toThrow('Receipt is not closed');
    });

    it('should throw for receipt with wrong gate', () => {
      const receipt = {
        ok: true,
        windowClosed: true,
        budgetAfter: { io: 0, cpuMs: 0, mem: 0 },
        details: { gate: GATES.RECEIPT }
      };
      
      expect(() => assertClosed(receipt, GATES.CONSERVATION)).toThrow('gate mismatch');
    });
  });

  describe('mkWitness', () => {
    it('should create valid witness', () => {
      const witness = mkWitness('test-r96');
      
      expect(witness).toBeValidWitness();
      expect(witness.r96).toBe('test-r96');
    });

    it('should use default node ID', () => {
      const witness = mkWitness('test-r96');
      
      expect(witness).toBeValidWitness();
      expect(witness.r96).toBe('test-r96');
    });
  });

  describe('uorIdFromBytes', () => {
    it('should generate UOR ID from bytes', () => {
      const bytes = Buffer.from('test data');
      const id = uorIdFromBytes(bytes);
      
      expect(id).toMatch(/^uor:[a-f0-9]{24}$/);
    });
  });

  describe('place', () => {
    it('should place data on lattice', () => {
      const coords = place('test-id', { rows: 48, cols: 256 });
      
      expect(coords).toHaveLength(3);
      coords.forEach(coord => {
        expect(coord).toBeValidLatticeCoord();
      });
    });
  });

  describe('validateCoords', () => {
    it('should validate correct coordinates', () => {
      const coords = [
        { r: 0, c: 0 },
        { r: 1, c: 100 },
        { r: 47, c: 255 }
      ];
      
      expect(() => validateCoords(coords)).not.toThrow();
    });

    it('should throw for insufficient coordinates', () => {
      const coords = [
        { r: 0, c: 0 },
        { r: 1, c: 100 }
      ];
      
      expect(() => validateCoords(coords)).toThrow('Insufficient coordinates');
    });

    it('should throw for invalid row', () => {
      const coords = [
        { r: 0, c: 0 },
        { r: 48, c: 100 }, // Invalid row
        { r: 1, c: 200 }
      ];
      
      expect(() => validateCoords(coords)).toThrow('Invalid row');
    });

    it('should throw for invalid column', () => {
      const coords = [
        { r: 0, c: 0 },
        { r: 1, c: 256 }, // Invalid column
        { r: 2, c: 200 }
      ];
      
      expect(() => validateCoords(coords)).toThrow('Invalid column');
    });

    it('should throw for insufficient row diversity', () => {
      const coords = [
        { r: 0, c: 0 },
        { r: 0, c: 100 }, // Same row
        { r: 0, c: 200 }  // Same row
      ];
      
      expect(() => validateCoords(coords)).toThrow('Insufficient row diversity');
    });
  });

  describe('mkMatrixBlock', () => {
    it('should create matrix block', () => {
      const block = mkMatrixBlock(4, 42);
      
      expect(block).toBeInstanceOf(Buffer);
      expect(block.length).toBe(4 * 4 * 2); // 4x4 matrix, 2 bytes per int16
    });
  });

  describe('measureTime', () => {
    it('should measure execution time', async () => {
      const { result, duration } = await measureTime(async () => {
        await sleep(10);
        return 'test result';
      });
      
      expect(result).toBe('test result');
      expect(duration).toBeGreaterThanOrEqual(10);
    });
  });

  describe('mkTransportFrame', () => {
    it('should create transport frame', () => {
      const payload = Buffer.from('test payload');
      const frame = mkTransportFrame(5, payload, 'W123');
      
      expect(frame.lane).toBe(5);
      expect(frame.payload).toBe(payload);
      expect(frame.windowId).toBe('W123');
      expect(frame.r96).toBeDefined();
      expect(frame.timestamp).toBeGreaterThan(0);
    });
  });

  describe('validateBudget', () => {
    it('should validate correct budget', () => {
      const b = budget(100, 50, 1024);
      
      expect(() => validateBudget(b)).not.toThrow();
    });

    it('should throw for negative values', () => {
      const b = { cpuMs: -1, io: 50, mem: 1024 };
      
      expect(() => validateBudget(b)).toThrow('negative values not allowed');
    });
  });

  describe('hasBudget', () => {
    it('should return true when budget is sufficient', () => {
      const available = budget(100, 50, 1024);
      const required = budget(50, 25, 512);
      
      expect(hasBudget(available, required)).toBe(true);
    });

    it('should return false when budget is insufficient', () => {
      const available = budget(50, 25, 512);
      const required = budget(100, 50, 1024);
      
      expect(hasBudget(available, required)).toBe(false);
    });
  });

  describe('mkStoragePolicy', () => {
    it('should create storage policy with defaults', () => {
      const policy = mkStoragePolicy();
      
      expect(policy).toEqual({
        replicas: 3,
        parity: 1,
        faultDomains: 2,
        ec: { k: 3, m: 1 }
      });
    });

    it('should create storage policy with custom values', () => {
      const policy = mkStoragePolicy(5, 2);
      
      expect(policy).toEqual({
        replicas: 5,
        parity: 2,
        faultDomains: 4,
        ec: { k: 5, m: 2 }
      });
    });
  });

  describe('mkTestData', () => {
    it('should create test data with default pattern', () => {
      const data = mkTestData(100);
      
      expect(data).toBeInstanceOf(Buffer);
      expect(data.length).toBe(100);
    });

    it('should create test data with custom pattern', () => {
      const data = mkTestData(50, 'ABC');
      
      expect(data).toBeInstanceOf(Buffer);
      expect(data.length).toBe(50);
    });
  });

  describe('mkComputeKernel', () => {
    it('should create compute kernel configuration', () => {
      const inputs = [{ id: 'input1' }, { id: 'input2' }];
      const budget = { cpuMs: 100, io: 10, mem: 1024 };
      
      const kernel = mkComputeKernel('test-kernel', inputs, budget);
      
      expect(kernel.name).toBe('test-kernel');
      expect(kernel.inputs).toBe(inputs);
      expect(kernel.budget).toBe(budget);
      expect(kernel.pin).toBeDefined();
      expect(kernel.iopolicy).toBeDefined();
    });
  });

  describe('sleep', () => {
    it('should sleep for specified duration', async () => {
      const start = Date.now();
      await sleep(10);
      const duration = Date.now() - start;
      
      expect(duration).toBeGreaterThanOrEqual(10);
    });
  });

  describe('mkNodeId', () => {
    it('should create node ID with default prefix', () => {
      const id = mkNodeId();
      
      expect(id).toMatch(/^test-\d+-[a-z0-9]{9}$/);
    });

    it('should create node ID with custom prefix', () => {
      const id = mkNodeId('custom');
      
      expect(id).toMatch(/^custom-\d+-[a-z0-9]{9}$/);
    });
  });

  describe('validateReceipt', () => {
    it('should validate correct receipt', () => {
      const receipt = {
        ok: true,
        windowClosed: true,
        budgetAfter: { io: 0, cpuMs: 0, mem: 0 },
        details: { gate: GATES.RECEIPT }
      };
      
      expect(() => validateReceipt(receipt)).not.toThrow();
    });

    it('should throw for invalid receipt', () => {
      const receipt = {
        ok: 'invalid',
        windowClosed: true,
        budgetAfter: { io: 0, cpuMs: 0, mem: 0 },
        details: { gate: GATES.RECEIPT }
      } as any;
      
      expect(() => validateReceipt(receipt)).toThrow('Receipt ok field must be boolean');
    });
  });

  describe('mkAdapter', () => {
    it('should return adapter instance', () => {
      const adapter = mkAdapter();
      
      expect(adapter).toBeDefined();
      expect(adapter.createVerifier).toBeInstanceOf(Function);
      expect(adapter.createCTP).toBeInstanceOf(Function);
      expect(adapter.createStorage).toBeInstanceOf(Function);
      expect(adapter.spawnKernel).toBeInstanceOf(Function);
    });
  });
});

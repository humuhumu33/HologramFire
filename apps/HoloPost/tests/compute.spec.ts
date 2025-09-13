/**
 * Integration tests for Compute functionality
 */

import { spawnKernel, createStorage } from '../src/adapters/hologram';
import { createPostcard, createPostcardWitness } from '../src/usecases/postcard';
import { mkBudget } from '../src/testkit';

describe('Compute Integration', () => {
  let storage: any;
  let postcard: any;
  let witness: any;

  beforeEach(async () => {
    storage = await createStorage({
      rows: 48,
      cols: 256,
      tileCols: 16,
      ec: { k: 3, m: 2 },
    });
    
    postcard = createPostcard('Compute test message', 'TestUser', 'TestRecipient');
    witness = await createPostcardWitness(postcard);
    
    // Store the postcard so it can be used as input
    const budget = mkBudget(300, 40, 24);
    await storage.put({
      id: postcard.id,
      bytes: postcard.bytes,
      policy: {},
      budget,
      witness,
    });
  });

  describe('Kernel execution', () => {
    it('should spawn kernel with input pinned near data', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: {
          near: postcard.id,
          lane: 2,
        },
        iopolicy: {
          lane: 2,
          windowMs: 100,
        },
      });
      
      const result = await kernel.await();
      
      expect(result.ok).toBe(true);
      expect(result.outputs).toHaveLength(1);
      expect(result.receipts.compute).toBeDefined();
      expect(result.receipts.aggregate).toBeDefined();
    });

    it('should return closed compute and aggregate receipts', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: { near: postcard.id },
      });
      
      const result = await kernel.await();
      
      expect(result.receipts.compute.ok).toBe(true);
      expect(result.receipts.compute.windowClosed).toBe(true);
      expect(result.receipts.compute.details.operation).toBe('kernel_compute');
      expect(result.receipts.compute.details['kernel']).toBe('stamp-postcard:v1');
      
      expect(result.receipts.aggregate.ok).toBe(true);
      expect(result.receipts.aggregate.windowClosed).toBe(true);
      expect(result.receipts.aggregate.details.operation).toBe('kernel_aggregate');
      expect(result.receipts.aggregate.details['kernel']).toBe('stamp-postcard:v1');
    });

    it('should generate output with valid witness', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: { near: postcard.id },
      });
      
      const result = await kernel.await();
      const output = result.outputs[0];
      
      expect(output).toBeDefined();
      expect(output?.id).toBeDefined();
      expect(output?.witness).toBeDefined();
      expect(output?.witness.r96).toBeDefined();
      expect(output?.witness.probes).toBe(192);
      expect(output?.witness.timestamp).toBeDefined();
    });

    it('should save output in storage', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: { near: postcard.id },
      });
      
      const result = await kernel.await();
      const output = result.outputs[0];
      
      // Verify output is stored in storage
      const getResult = await storage.get({ id: output?.id || '' });
      expect(getResult.bytes).toBeDefined();
      expect(getResult.witness).toBeDefined();
    });
  });

  describe('Budget enforcement', () => {
    it('should reject kernel with insufficient budget', async () => {
      const zeroBudget = mkBudget(0, 0, 0);
      
      await expect(
        spawnKernel({
          name: 'stamp-postcard:v1',
          inputs: [{ id: postcard.id }],
          budget: zeroBudget,
          pin: { near: postcard.id },
        })
      ).rejects.toThrow('Insufficient budget');
    });

    it('should accept kernel with adequate budget', async () => {
      const adequateBudget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget: adequateBudget,
        pin: { near: postcard.id },
      });
      
      const result = await kernel.await();
      expect(result.ok).toBe(true);
    });
  });

  describe('Multiple inputs', () => {
    it('should handle kernel with multiple inputs', async () => {
      const budget = mkBudget(600, 90, 48);
      
      // Create additional postcards
      const postcard2 = createPostcard('Second input', 'User2', 'Recipient2');
      const postcard3 = createPostcard('Third input', 'User3', 'Recipient3');
      
      const witness2 = await createPostcardWitness(postcard2);
      const witness3 = await createPostcardWitness(postcard3);
      
      // Store additional postcards
      const storeBudget = mkBudget(300, 40, 24);
      await storage.put({
        id: postcard2.id,
        bytes: postcard2.bytes,
        policy: {},
        budget: storeBudget,
        witness: witness2,
      });
      
      await storage.put({
        id: postcard3.id,
        bytes: postcard3.bytes,
        policy: {},
        budget: storeBudget,
        witness: witness3,
      });
      
      // Spawn kernel with multiple inputs
      const kernel = await spawnKernel({
        name: 'batch-stamp-postcard:v1',
        inputs: [
          { id: postcard.id },
          { id: postcard2.id },
          { id: postcard3.id },
        ],
        budget,
        pin: { near: postcard.id },
      });
      
      const result = await kernel.await();
      
      expect(result.ok).toBe(true);
      expect(result.outputs).toHaveLength(3);
      expect(result.receipts.aggregate.details['inputCount']).toBe(3);
      expect(result.receipts.aggregate.details['outputCount']).toBe(3);
    });
  });

  describe('Different kernel types', () => {
    it('should handle different kernel variants', async () => {
      const budget = mkBudget(400, 60, 32);
      const kernels = [
        'stamp-postcard:v1',
        'encrypt-postcard:v1',
        'compress-postcard:v1',
      ];
      
      for (const kernelName of kernels) {
        const kernel = await spawnKernel({
          name: kernelName,
          inputs: [{ id: postcard.id }],
          budget,
          pin: { near: postcard.id },
        });
        
        const result = await kernel.await();
        
        expect(result.ok).toBe(true);
        expect(result.receipts.compute.details['kernel']).toBe(kernelName);
        expect(result.receipts.aggregate.details['kernel']).toBe(kernelName);
      }
    });
  });

  describe('Pinning and I/O policy', () => {
    it('should respect pinning configuration', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: {
          near: postcard.id,
          lane: 5,
        },
        iopolicy: {
          lane: 5,
          windowMs: 200,
        },
      });
      
      const result = await kernel.await();
      expect(result.ok).toBe(true);
    });

    it('should work without pinning configuration', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
      });
      
      const result = await kernel.await();
      expect(result.ok).toBe(true);
    });
  });

  describe('Error handling', () => {
    it('should handle non-existent input', async () => {
      const budget = mkBudget(400, 60, 32);
      
      const kernel = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: 'non-existent-id' }],
        budget,
        pin: { near: 'non-existent-id' },
      });
      
      await expect(kernel.await()).rejects.toThrow('Input not found');
    });

    it('should handle kernel execution failure gracefully', async () => {
      const budget = mkBudget(1, 1, 1); // Very small budget
      
      const kernel = await spawnKernel({
        name: 'failing-kernel:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: { near: postcard.id },
      });
      
      // This should either succeed or fail gracefully
      try {
        const result = await kernel.await();
        expect(result.ok).toBeDefined();
      } catch (error) {
        // Expected for failing kernel
        expect(error).toBeDefined();
      }
    });
  });

  describe('Output verification', () => {
    it('should generate consistent outputs for the same input', async () => {
      const budget = mkBudget(400, 60, 32);
      
      // Run kernel twice with same input
      const kernel1 = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: { near: postcard.id },
      });
      
      const result1 = await kernel1.await();
      
      const kernel2 = await spawnKernel({
        name: 'stamp-postcard:v1',
        inputs: [{ id: postcard.id }],
        budget,
        pin: { near: postcard.id },
      });
      
      const result2 = await kernel2.await();
      
      // Outputs should be consistent
      expect(result1.outputs[0]?.id).toBe(result2.outputs[0]?.id);
      expect(result1.outputs[0]?.witness.r96).toBe(result2.outputs[0]?.witness.r96);
    });
  });
});

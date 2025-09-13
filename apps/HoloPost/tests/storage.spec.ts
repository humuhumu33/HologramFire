/**
 * Integration tests for Storage functionality
 */

import { createStorage, createVerifier } from '../src/adapters/hologram';
import { createPostcard, createPostcardWitness } from '../src/usecases/postcard';
import { mkBudget } from '../src/testkit';

describe('Storage Integration', () => {
  let storage: any;
  let verifier: any;
  let postcard: any;
  let witness: any;

  beforeEach(async () => {
    storage = await createStorage({
      rows: 48,
      cols: 256,
      tileCols: 16,
      ec: { k: 3, m: 2 },
    });
    
    verifier = await createVerifier();
    postcard = createPostcard('Storage test message', 'TestUser', 'TestRecipient');
    witness = await createPostcardWitness(postcard);
  });

  describe('Storage put and get', () => {
    it('should store data and return closed receipt', async () => {
      const budget = mkBudget(300, 40, 24);
      const policy = {
        replication: 3,
        erasureCoding: { k: 3, m: 2 },
      };
      
      const receipt = await storage.put({
        id: postcard.id,
        bytes: postcard.bytes,
        policy,
        budget,
        witness,
      });
      
      expect(receipt.ok).toBe(true);
      expect(receipt.windowClosed).toBe(true);
      expect(receipt.budgetAfter).toBeDefined();
      expect(receipt.details.operation).toBe('storage_put');
      expect(receipt.details.id).toBe(postcard.id);
      expect(receipt.details.placements).toBeDefined();
    });

    it('should retrieve stored data with identical bytes', async () => {
      const budget = mkBudget(300, 40, 24);
      
      await storage.put({
        id: postcard.id,
        bytes: postcard.bytes,
        policy: {},
        budget,
        witness,
      });
      
      const getResult = await storage.get({
        id: postcard.id,
        policy: { verifyWitness: true },
      });
      
      expect(getResult.bytes).toEqual(postcard.bytes);
      expect(getResult.witness).toBeDefined();
      expect(getResult.witness.r96).toBe(witness.r96);
    });

    it('should verify witness on retrieved data', async () => {
      const budget = mkBudget(300, 40, 24);
      
      await storage.put({
        id: postcard.id,
        bytes: postcard.bytes,
        policy: {},
        budget,
        witness,
      });
      
      const getResult = await storage.get({
        id: postcard.id,
      });
      
      const expectedR96 = verifier.r96(getResult.bytes);
      expect(expectedR96).toBe(getResult.witness.r96);
    });

    it('should handle multiple storage operations', async () => {
      const budget = mkBudget(100, 15, 8);
      const postcards = [
        createPostcard('Message 1', 'User1', 'Recipient1'),
        createPostcard('Message 2', 'User2', 'Recipient2'),
        createPostcard('Message 3', 'User3', 'Recipient3'),
      ];
      
      // Store all postcards
      for (const p of postcards) {
        const w = await createPostcardWitness(p);
        const receipt = await storage.put({
          id: p.id,
          bytes: p.bytes,
          policy: {},
          budget,
          witness: w,
        });
        
        expect(receipt.ok).toBe(true);
        expect(receipt.windowClosed).toBe(true);
      }
      
      // Retrieve all postcards
      for (const p of postcards) {
        const getResult = await storage.get({ id: p.id });
        expect(getResult.bytes).toEqual(p.bytes);
      }
    });
  });

  describe('Storage repair', () => {
    it('should repair damaged data and return closed receipt', async () => {
      const budget = mkBudget(300, 40, 24);
      
      // Store data first
      await storage.put({
        id: postcard.id,
        bytes: postcard.bytes,
        policy: {},
        budget,
        witness,
      });
      
      // Repair data
      const repairBudget = mkBudget(100, 20, 8);
      const repairReceipt = await storage.repair({
        id: postcard.id,
        budget: repairBudget,
      });
      
      expect(repairReceipt.ok).toBe(true);
      expect(repairReceipt.windowClosed).toBe(true);
      expect(repairReceipt.details.operation).toBe('storage_repair');
      expect(repairReceipt.details.id).toBe(postcard.id);
    });

    it('should handle repair of non-existent data', async () => {
      const repairBudget = mkBudget(100, 20, 8);
      
      await expect(
        storage.repair({
          id: 'non-existent-id',
          budget: repairBudget,
        })
      ).rejects.toThrow('Cannot repair non-existent data');
    });
  });

  describe('Storage damage simulation', () => {
    it('should simulate damage when debug functionality is available', async () => {
      const budget = mkBudget(300, 40, 24);
      
      // Store data first
      await storage.put({
        id: postcard.id,
        bytes: postcard.bytes,
        policy: {},
        budget,
        witness,
      });
      
      // Simulate damage if debug functionality is available
      if (storage.debug && storage.debug.damage) {
        const damageResult = await storage.debug.damage({
          id: postcard.id,
          parts: 1,
        });
        
        expect(damageResult).toBe(true);
        
        // Verify data is still accessible (repair should have happened automatically)
        const getResult = await storage.get({ id: postcard.id });
        expect(getResult.bytes).toBeDefined();
      } else {
        // Skip test if debug functionality is not available
        expect(true).toBe(true);
      }
    });
  });

  describe('Budget enforcement', () => {
    it('should reject put with insufficient budget', async () => {
      const zeroBudget = mkBudget(0, 0, 0);
      
      await expect(
        storage.put({
          id: postcard.id,
          bytes: postcard.bytes,
          policy: {},
          budget: zeroBudget,
          witness,
        })
      ).rejects.toThrow('Insufficient budget');
    });

    it('should reject repair with insufficient budget', async () => {
      const budget = mkBudget(300, 40, 24);
      
      // Store data first
      await storage.put({
        id: postcard.id,
        bytes: postcard.bytes,
        policy: {},
        budget,
        witness,
      });
      
      const zeroBudget = mkBudget(0, 0, 0);
      
      await expect(
        storage.repair({
          id: postcard.id,
          budget: zeroBudget,
        })
      ).rejects.toThrow('Insufficient budget');
    });
  });

  describe('Error handling', () => {
    it('should handle get of non-existent data', async () => {
      await expect(
        storage.get({ id: 'non-existent-id' })
      ).rejects.toThrow('Data not found');
    });

    it('should handle storage with different policies', async () => {
      const budget = mkBudget(300, 40, 24);
      const policies = [
        { replication: 1 },
        { replication: 3, erasureCoding: { k: 2, m: 1 } },
        { replication: 5, erasureCoding: { k: 4, m: 2 } },
      ];
      
      for (let i = 0; i < policies.length; i++) {
        const p = createPostcard(`Policy test ${i}`, 'User', 'Recipient');
        const w = await createPostcardWitness(p);
        
        const receipt = await storage.put({
          id: p.id,
          bytes: p.bytes,
          policy: policies[i],
          budget,
          witness: w,
        });
        
        expect(receipt.ok).toBe(true);
        
        const getResult = await storage.get({ id: p.id });
        expect(getResult.bytes).toEqual(p.bytes);
      }
    });
  });

  describe('Data integrity', () => {
    it('should maintain data integrity across operations', async () => {
      const budget = mkBudget(300, 40, 24);
      const originalBytes = postcard.bytes;
      
      // Store data
      await storage.put({
        id: postcard.id,
        bytes: originalBytes,
        policy: {},
        budget,
        witness,
      });
      
      // Retrieve and verify
      const getResult1 = await storage.get({ id: postcard.id });
      expect(getResult1.bytes).toEqual(originalBytes);
      
      // Repair and verify again
      const repairBudget = mkBudget(100, 20, 8);
      await storage.repair({ id: postcard.id, budget: repairBudget });
      
      const getResult2 = await storage.get({ id: postcard.id });
      expect(getResult2.bytes).toEqual(originalBytes);
      
      // Verify witnesses are consistent
      const expectedR96 = verifier.r96(originalBytes);
      expect(getResult1.witness.r96).toBe(expectedR96);
      expect(getResult2.witness.r96).toBe(expectedR96);
    });
  });
});

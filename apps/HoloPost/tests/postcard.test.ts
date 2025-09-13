/**
 * Unit tests for Postcard functionality
 */

import {
  createPostcard,
  validatePostcard,
  createPostcardWitness,
  getPostcardPlacement,
  createSamplePostcard,
  createBatchPostcards,
  comparePostcards,
  getPostcardMetadata,
} from '../src/usecases/postcard';

describe('Postcard', () => {
  describe('createPostcard', () => {
    it('should create a postcard with all required fields', () => {
      const postcard = createPostcard('Hello, World!', 'Alice', 'Bob');
      
      expect(postcard).toHaveProperty('id');
      expect(postcard).toHaveProperty('message', 'Hello, World!');
      expect(postcard).toHaveProperty('from', 'Alice');
      expect(postcard).toHaveProperty('to', 'Bob');
      expect(postcard).toHaveProperty('timestamp');
      expect(postcard).toHaveProperty('bytes');
      
      expect(typeof postcard.id).toBe('string');
      expect(typeof postcard.message).toBe('string');
      expect(typeof postcard.from).toBe('string');
      expect(typeof postcard.to).toBe('string');
      expect(typeof postcard.timestamp).toBe('number');
      expect(Buffer.isBuffer(postcard.bytes)).toBe(true);
    });

    it('should use default values when not provided', () => {
      const postcard = createPostcard('Test message');
      
      expect(postcard.from).toBe('Alice');
      expect(postcard.to).toBe('Bob');
    });

    it('should generate consistent IDs for the same content', () => {
      const postcard1 = createPostcard('Hello, World!', 'Alice', 'Bob');
      const postcard2 = createPostcard('Hello, World!', 'Alice', 'Bob');
      
      expect(postcard1.id).toBe(postcard2.id);
    });

    it('should generate different IDs for different content', () => {
      const postcard1 = createPostcard('Hello, World!', 'Alice', 'Bob');
      const postcard2 = createPostcard('Hello, Universe!', 'Alice', 'Bob');
      
      expect(postcard1.id).not.toBe(postcard2.id);
    });
  });

  describe('validatePostcard', () => {
    it('should validate a correct postcard', async () => {
      const postcard = createPostcard('Valid message', 'Alice', 'Bob');
      const isValid = await validatePostcard(postcard);
      
      expect(isValid).toBe(true);
    });

    it('should reject postcard with mismatched ID', async () => {
      const postcard = createPostcard('Test message', 'Alice', 'Bob');
      postcard.id = 'wrong-id';
      
      const isValid = await validatePostcard(postcard);
      expect(isValid).toBe(false);
    });

    it('should reject postcard with corrupted content', async () => {
      const postcard = createPostcard('Test message', 'Alice', 'Bob');
      postcard.bytes = Buffer.from('corrupted content');
      
      const isValid = await validatePostcard(postcard);
      expect(isValid).toBe(false);
    });
  });

  describe('createPostcardWitness', () => {
    it('should create a witness with all required fields', async () => {
      const postcard = createPostcard('Test message', 'Alice', 'Bob');
      const witness = await createPostcardWitness(postcard);
      
      expect(witness).toHaveProperty('r96');
      expect(witness).toHaveProperty('probes');
      expect(witness).toHaveProperty('timestamp');
      
      expect(typeof witness.r96).toBe('string');
      expect(typeof witness.probes).toBe('number');
      expect(typeof witness.timestamp).toBe('number');
      
      expect(witness.r96).toHaveLength(24);
      expect(witness.probes).toBe(192);
    });

    it('should create consistent witnesses for the same postcard', async () => {
      const postcard = createPostcard('Test message', 'Alice', 'Bob');
      const witness1 = await createPostcardWitness(postcard);
      const witness2 = await createPostcardWitness(postcard);
      
      expect(witness1.r96).toBe(witness2.r96);
      expect(witness1.probes).toBe(witness2.probes);
    });
  });

  describe('getPostcardPlacement', () => {
    it('should return valid placements', () => {
      const postcard = createPostcard('Test message', 'Alice', 'Bob');
      const placements = getPostcardPlacement(postcard);
      
      expect(Array.isArray(placements)).toBe(true);
      expect(placements.length).toBeGreaterThanOrEqual(3);
      
      placements.forEach(placement => {
        expect(placement).toHaveProperty('r');
        expect(placement).toHaveProperty('c');
        expect(typeof placement.r).toBe('number');
        expect(typeof placement.c).toBe('number');
        expect(placement.r).toBeGreaterThanOrEqual(0);
        expect(placement.r).toBeLessThan(48);
        expect(placement.c).toBeGreaterThanOrEqual(0);
        expect(placement.c).toBeLessThan(256);
      });
    });
  });

  describe('createSamplePostcard', () => {
    it('should create a postcard with sample data', () => {
      const postcard = createSamplePostcard();
      
      expect(postcard).toHaveProperty('id');
      expect(postcard).toHaveProperty('message');
      expect(postcard).toHaveProperty('from', 'HoloUser');
      expect(postcard).toHaveProperty('to', 'Friend');
      expect(postcard).toHaveProperty('timestamp');
      expect(postcard).toHaveProperty('bytes');
      
      expect(postcard.message.length).toBeGreaterThan(0);
    });
  });

  describe('createBatchPostcards', () => {
    it('should create the specified number of postcards', () => {
      const count = 5;
      const postcards = createBatchPostcards(count);
      
      expect(postcards).toHaveLength(count);
      
      postcards.forEach((postcard, index) => {
        expect(postcard.from).toBe(`User${index + 1}`);
        expect(postcard.to).toBe(`Recipient${index + 1}`);
        expect(postcard.message).toContain(`Batch message #${index + 1}`);
      });
    });

    it('should create unique postcards', () => {
      const postcards = createBatchPostcards(3);
      const ids = postcards.map(p => p.id);
      const uniqueIds = new Set(ids);
      
      expect(uniqueIds.size).toBe(ids.length);
    });
  });

  describe('comparePostcards', () => {
    it('should return true for identical postcards', () => {
      const postcard1 = createPostcard('Test message', 'Alice', 'Bob');
      const postcard2 = createPostcard('Test message', 'Alice', 'Bob');
      
      expect(comparePostcards(postcard1, postcard2)).toBe(true);
    });

    it('should return false for different postcards', () => {
      const postcard1 = createPostcard('Test message 1', 'Alice', 'Bob');
      const postcard2 = createPostcard('Test message 2', 'Alice', 'Bob');
      
      expect(comparePostcards(postcard1, postcard2)).toBe(false);
    });
  });

  describe('getPostcardMetadata', () => {
    it('should return all metadata fields', () => {
      const postcard = createPostcard('Test message', 'Alice', 'Bob');
      const metadata = getPostcardMetadata(postcard);
      
      expect(metadata).toHaveProperty('id');
      expect(metadata).toHaveProperty('size');
      expect(metadata).toHaveProperty('from');
      expect(metadata).toHaveProperty('to');
      expect(metadata).toHaveProperty('messageLength');
      expect(metadata).toHaveProperty('timestamp');
      
      expect(metadata.id).toBe(postcard.id);
      expect(metadata.size).toBe(postcard.bytes.length);
      expect(metadata.from).toBe(postcard.from);
      expect(metadata.to).toBe(postcard.to);
      expect(metadata.messageLength).toBe(postcard.message.length);
      expect(typeof metadata.timestamp).toBe('string');
    });
  });
});

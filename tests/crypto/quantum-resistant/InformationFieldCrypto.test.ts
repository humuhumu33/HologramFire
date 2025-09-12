/**
 * Tests for Information Field Quantum-Resistant Cryptographic System
 * 
 * These tests validate the quantum-resistant cryptographic system based on
 * information field conservation and coherence principles.
 */

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import {
  InformationFieldCrypto,
  FieldKey,
  CoherenceSignature,
  InformationField,
  QuantumResistantConfig,
  getQuantumResistantCrypto,
  generateQuantumResistantKey,
  createQuantumResistantSignature,
  verifyQuantumResistantSignature
} from "../../../src/crypto/quantum-resistant/InformationFieldCrypto";

describe("InformationFieldCrypto", () => {
  let crypto: InformationFieldCrypto;
  let config: QuantumResistantConfig;

  beforeEach(() => {
    config = {
      field_dimensions: 12288,
      coherence_threshold: 0.95,
      conservation_tolerance: 1e-6,
      resonance_bands: 96,
      holographic_depth: 7
    };
    crypto = new InformationFieldCrypto(config);
  });

  afterEach(() => {
    crypto.clearCache();
  });

  describe("Field Key Generation", () => {
    it("should generate a valid field key", async () => {
      const seed = "test_seed_123";
      const context = { test: true, domain: "test" };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      expect(fieldKey).toBeDefined();
      expect(fieldKey.field).toBeDefined();
      expect(fieldKey.klein_windows).toBeDefined();
      expect(fieldKey.c768_schedule).toBeDefined();
      expect(fieldKey.resonance_key).toBeDefined();
      expect(fieldKey.holographic_correspondence).toBeDefined();
    });

    it("should generate consistent field keys for same input", async () => {
      const seed = "consistent_seed";
      const context = { test: true };
      
      const key1 = await crypto.generateFieldKey(seed, context);
      const key2 = await crypto.generateFieldKey(seed, context);
      
      expect(key1.field.holographic_fingerprint).toBe(key2.field.holographic_fingerprint);
      expect(key1.resonance_key).toBe(key2.resonance_key);
      expect(key1.holographic_correspondence).toBe(key2.holographic_correspondence);
    });

    it("should generate different field keys for different inputs", async () => {
      const seed1 = "seed_1";
      const seed2 = "seed_2";
      const context = { test: true };
      
      const key1 = await crypto.generateFieldKey(seed1, context);
      const key2 = await crypto.generateFieldKey(seed2, context);
      
      expect(key1.field.holographic_fingerprint).not.toBe(key2.field.holographic_fingerprint);
      expect(key1.resonance_key).not.toBe(key2.resonance_key);
    });

    it("should have valid field properties", async () => {
      const seed = "validation_seed";
      const context = { test: true };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      // Test field coherence
      expect(fieldKey.field.coherence).toBeGreaterThanOrEqual(0);
      expect(fieldKey.field.coherence).toBeLessThanOrEqual(1);
      
      // Test conservation
      expect(fieldKey.field.conservation).toBeGreaterThanOrEqual(0);
      expect(fieldKey.field.conservation).toBeLessThanOrEqual(1);
      
      // Test resonance spectrum
      expect(fieldKey.field.resonance).toHaveLength(96);
      expect(fieldKey.field.resonance.every(r => r >= 0 && r <= 1)).toBe(true);
      
      // Test holographic fingerprint
      expect(fieldKey.field.holographic_fingerprint).toBeDefined();
      expect(typeof fieldKey.field.holographic_fingerprint).toBe("string");
    });

    it("should have valid Klein windows", async () => {
      const seed = "klein_test_seed";
      const context = { test: true };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      expect(fieldKey.klein_windows).toHaveLength(192);
      
      // Test Klein window properties
      for (const window of fieldKey.klein_windows || []) {
        expect(window.id).toBeGreaterThanOrEqual(0);
        expect(window.id).toBeLessThan(192);
        expect(window.shape).toEqual([48, 256]);
        expect(typeof window.map).toBe("function");
      }
    });

    it("should have valid C768 schedule", async () => {
      const seed = "c768_test_seed";
      const context = { test: true };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      expect(fieldKey.c768_schedule).toHaveLength(768);
      
      // Test C768 schedule properties
      const seen = new Set<number>();
      let sum = 0;
      
      for (const value of fieldKey.c768_schedule || []) {
        expect(value).toBeGreaterThanOrEqual(0);
        expect(value).toBeLessThan(768);
        expect(Number.isInteger(value)).toBe(true);
        expect(seen.has(value)).toBe(false);
        seen.add(value);
        sum += value;
      }
      
      const expectedSum = (768 * (768 - 1)) / 2;
      expect(sum).toBe(expectedSum);
    });
  });

  describe("Coherence Signature Creation", () => {
    let fieldKey: FieldKey;

    beforeEach(async () => {
      const seed = "signature_test_seed";
      const context = { test: true };
      fieldKey = await crypto.generateFieldKey(seed, context);
    });

    it("should create a valid coherence signature", async () => {
      const message = { test: "message", data: [1, 2, 3] };
      
      const signature = await crypto.createCoherenceSignature(message, fieldKey);
      
      expect(signature).toBeDefined();
      expect(signature.field_coherence).toBeGreaterThanOrEqual(0);
      expect(signature.field_coherence).toBeLessThanOrEqual(1);
      expect(signature.conservation_proof).toBeDefined();
      expect(signature.resonance_spectrum).toHaveLength(96);
      expect(signature.holographic_correspondence).toBeDefined();
      expect(signature.field_topology).toBeDefined();
    });

    it("should create consistent signatures for same input", async () => {
      const message = { test: "consistent_message" };
      
      const signature1 = await crypto.createCoherenceSignature(message, fieldKey);
      const signature2 = await crypto.createCoherenceSignature(message, fieldKey);
      
      expect(signature1.field_coherence).toBe(signature2.field_coherence);
      expect(signature1.conservation_proof).toBe(signature2.conservation_proof);
      expect(signature1.holographic_correspondence).toBe(signature2.holographic_correspondence);
      expect(signature1.field_topology).toBe(signature2.field_topology);
    });

    it("should create different signatures for different inputs", async () => {
      const message1 = { test: "message_1" };
      const message2 = { test: "message_2" };
      
      const signature1 = await crypto.createCoherenceSignature(message1, fieldKey);
      const signature2 = await crypto.createCoherenceSignature(message2, fieldKey);
      
      expect(signature1.conservation_proof).not.toBe(signature2.conservation_proof);
      expect(signature1.holographic_correspondence).not.toBe(signature2.holographic_correspondence);
      expect(signature1.field_topology).not.toBe(signature2.field_topology);
    });
  });

  describe("Coherence Signature Verification", () => {
    let fieldKey: FieldKey;

    beforeEach(async () => {
      const seed = "verification_test_seed";
      const context = { test: true };
      fieldKey = await crypto.generateFieldKey(seed, context);
    });

    it("should verify valid signatures", async () => {
      const message = { test: "verification_message" };
      
      const signature = await crypto.createCoherenceSignature(message, fieldKey);
      const isValid = await crypto.verifyCoherenceSignature(message, signature, fieldKey);
      
      expect(isValid).toBe(true);
    });

    it("should reject invalid signatures", async () => {
      const message = { test: "verification_message" };
      const wrongMessage = { test: "wrong_message" };
      
      const signature = await crypto.createCoherenceSignature(message, fieldKey);
      const isValid = await crypto.verifyCoherenceSignature(wrongMessage, signature, fieldKey);
      
      expect(isValid).toBe(false);
    });

    it("should reject tampered signatures", async () => {
      const message = { test: "tamper_test_message" };
      
      const signature = await crypto.createCoherenceSignature(message, fieldKey);
      
      // Tamper with signature
      const tamperedSignature = {
        ...signature,
        field_coherence: 0.5 // Change coherence value
      };
      
      const isValid = await crypto.verifyCoherenceSignature(message, tamperedSignature, fieldKey);
      
      expect(isValid).toBe(false);
    });

    it("should reject signatures with wrong field key", async () => {
      const message = { test: "wrong_key_test" };
      const wrongSeed = "wrong_seed";
      const wrongContext = { test: false };
      
      const signature = await crypto.createCoherenceSignature(message, fieldKey);
      const wrongFieldKey = await crypto.generateFieldKey(wrongSeed, wrongContext);
      
      const isValid = await crypto.verifyCoherenceSignature(message, signature, wrongFieldKey);
      
      expect(isValid).toBe(false);
    });
  });

  describe("Conservation Principles", () => {
    it("should maintain conservation invariants", async () => {
      const seed = "conservation_test_seed";
      const context = { test: true };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      // Test that field maintains conservation
      expect(fieldKey.field.conservation).toBeGreaterThanOrEqual(0.9);
    });

    it("should maintain coherence invariants", async () => {
      const seed = "coherence_test_seed";
      const context = { test: true };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      // Test that field maintains coherence
      expect(fieldKey.field.coherence).toBeGreaterThanOrEqual(0.9);
    });

    it("should maintain holographic correspondence", async () => {
      const seed = "holographic_test_seed";
      const context = { test: true };
      
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      // Test that holographic correspondence is maintained
      expect(fieldKey.holographic_correspondence).toBeDefined();
      expect(typeof fieldKey.holographic_correspondence).toBe("string");
      expect(fieldKey.holographic_correspondence?.length || 0).toBeGreaterThan(0);
    });
  });

  describe("Performance and Caching", () => {
    it("should cache field generation results", async () => {
      const seed = "cache_test_seed";
      const context = { test: true };
      
      // First generation
      const start1 = performance.now();
      const fieldKey1 = await crypto.generateFieldKey(seed, context);
      const time1 = performance.now() - start1;
      
      // Second generation (should use cache)
      const start2 = performance.now();
      const fieldKey2 = await crypto.generateFieldKey(seed, context);
      const time2 = performance.now() - start2;
      
      expect(fieldKey1.field.holographic_fingerprint).toBe(fieldKey2.field.holographic_fingerprint);
      expect(time2).toBeLessThan(time1); // Cached should be faster
    });

    it("should provide cache statistics", async () => {
      const stats = crypto.getCacheStats();
      
      expect(stats).toBeDefined();
      expect(stats.size).toBeGreaterThanOrEqual(0);
      expect(stats.hit_rate).toBeGreaterThanOrEqual(0);
      expect(stats.hit_rate).toBeLessThanOrEqual(1);
    });

    it("should clear cache when requested", async () => {
      const seed = "clear_cache_test";
      const context = { test: true };
      
      // Generate field to populate cache
      await crypto.generateFieldKey(seed, context);
      
      const statsBefore = crypto.getCacheStats();
      expect(statsBefore.size).toBeGreaterThan(0);
      
      // Clear cache
      crypto.clearCache();
      
      const statsAfter = crypto.getCacheStats();
      expect(statsAfter.size).toBe(0);
    });
  });

  describe("Global Functions", () => {
    it("should work with global crypto instance", async () => {
      const globalCrypto = getQuantumResistantCrypto();
      expect(globalCrypto).toBeDefined();
      expect(globalCrypto).toBeInstanceOf(InformationFieldCrypto);
    });

    it("should work with convenience functions", async () => {
      const seed = "convenience_test_seed";
      const context = { test: true };
      
      const fieldKey = await generateQuantumResistantKey(seed, context);
      expect(fieldKey).toBeDefined();
      
      const message = { test: "convenience_message" };
      const signature = await createQuantumResistantSignature(message, fieldKey);
      expect(signature).toBeDefined();
      
      const isValid = await verifyQuantumResistantSignature(message, signature, fieldKey);
      expect(isValid).toBe(true);
    });
  });

  describe("Error Handling", () => {
    it("should handle invalid inputs gracefully", async () => {
      const seed = "";
      const context = null;
      
      // Should not throw error
      const fieldKey = await crypto.generateFieldKey(seed, context);
      expect(fieldKey).toBeDefined();
    });

    it("should handle verification errors gracefully", async () => {
      const message = { test: "error_test" };
      const seed = "error_test_seed";
      const context = { test: true };
      const fieldKey = await crypto.generateFieldKey(seed, context);
      
      const invalidSignature = {
        signature: "invalid",
        fieldKey: fieldKey,
        timestamp: Date.now(),
        field_coherence: 0.5,
        conservation_proof: "invalid",
        resonance_spectrum: new Array(96).fill(0),
        holographic_correspondence: "invalid",
        field_topology: "invalid"
      };
      
      const isValid = await crypto.verifyCoherenceSignature(message, invalidSignature, fieldKey);
      expect(isValid).toBe(false);
    });
  });

  describe("Configuration", () => {
    it("should respect configuration parameters", async () => {
      const customConfig: QuantumResistantConfig = {
        field_dimensions: 6144,
        coherence_threshold: 0.9,
        conservation_tolerance: 1e-5,
        resonance_bands: 48,
        holographic_depth: 5
      };
      
      const customCrypto = new InformationFieldCrypto(customConfig);
      const seed = "config_test_seed";
      const context = { test: true };
      
      const fieldKey = await customCrypto.generateFieldKey(seed, context);
      
      expect(fieldKey.field.resonance).toHaveLength(48);
    });
  });
});

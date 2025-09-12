/**
 * Quantum-Resistant Cryptographic System
 * 
 * This module provides a complete quantum-resistant cryptographic system based on:
 * 1. Information field conservation and coherence principles
 * 2. Resonance-based encryption and authentication
 * 3. Holographic signatures and verification
 * 4. Conservation-based challenge-response protocols
 * 
 * Security is achieved through fundamental properties of information conservation
 * and field coherence rather than computational hardness assumptions.
 */

import { ccmHash } from "../ccm/CCMHash";
import { P, C, N } from "../../core/constants";

// Core quantum-resistant cryptographic primitives
export {
  InformationFieldCrypto,
  FieldKey,
  CoherenceSignature,
  InformationField,
  QuantumResistantConfig,
  getQuantumResistantCrypto,
  generateQuantumResistantKey,
  createQuantumResistantSignature,
  verifyQuantumResistantSignature
} from "./InformationFieldCrypto";

// Resonance-based encryption
export {
  ResonanceEncryption,
  ResonanceCiphertext,
  ResonanceDecryptionResult,
  ResonanceEncryptionConfig,
  getResonanceEncryption,
  encryptWithResonance,
  decryptWithResonance
} from "./ResonanceEncryption";

// Conservation-based authentication
export {
  ConservationBasedAuth,
  ConservationChallenge,
  ConservationResponse,
  ConservationAuthResult,
  ConservationAuthConfig,
  getConservationBasedAuth,
  generateConservationChallenge,
  verifyConservationResponse,
  verifyConservationSession
} from "./ConservationBasedAuth";

// Re-export core dependencies for convenience
export {
  generateKleinWindows,
  KleinWindow
} from "../../core/klein/Klein";

export {
  generateC768Schedule,
  verifyC768Schedule
} from "../../core/conservation/C768";

export {
  classifyR96,
  classifyR96Scalar
} from "../../core/resonance/R96";

export {
  phi
} from "../../core/holography/Phi";

export {
  N, P, C, R_CLASSES
} from "../../core/constants";

export {
  ccmHash
} from "../ccm/CCMHash";

// JSON error handling utilities are defined below and exported inline

/**
 * Quantum-Resistant Cryptographic System Factory
 * 
 * Creates a complete quantum-resistant cryptographic system with all components
 * configured for optimal performance and security.
 */
export class QuantumResistantCryptoSystem {
  private fieldCrypto: import("./InformationFieldCrypto").InformationFieldCrypto;
  private resonanceEncryption: import("./ResonanceEncryption").ResonanceEncryption;
  private conservationAuth: import("./ConservationBasedAuth").ConservationBasedAuth;

  constructor(config?: {
    fieldCrypto?: Partial<import("./InformationFieldCrypto").QuantumResistantConfig>;
    resonanceEncryption?: Partial<import("./ResonanceEncryption").ResonanceEncryptionConfig>;
    conservationAuth?: Partial<import("./ConservationBasedAuth").ConservationAuthConfig>;
  }) {
    // Use direct imports instead of require
    const { InformationFieldCrypto } = require("./InformationFieldCrypto");
    const { ResonanceEncryption } = require("./ResonanceEncryption");
    const { ConservationBasedAuth } = require("./ConservationBasedAuth");
    
    this.fieldCrypto = new InformationFieldCrypto(config?.fieldCrypto);
    this.resonanceEncryption = new ResonanceEncryption(config?.resonanceEncryption);
    this.conservationAuth = new ConservationBasedAuth(config?.conservationAuth);
  }

  /**
   * Get the information field crypto component
   */
  getFieldCrypto(): import("./InformationFieldCrypto").InformationFieldCrypto {
    return this.fieldCrypto;
  }

  /**
   * Get the resonance encryption component
   */
  getResonanceEncryption(): import("./ResonanceEncryption").ResonanceEncryption {
    return this.resonanceEncryption;
  }

  /**
   * Get the conservation-based authentication component
   */
  getConservationAuth(): import("./ConservationBasedAuth").ConservationBasedAuth {
    return this.conservationAuth;
  }

  /**
   * Generate a complete quantum-resistant key pair
   */
  async generateKeyPair(seed: string, context: unknown): Promise<{
    fieldKey: import("./InformationFieldCrypto").FieldKey;
    publicKey: string;
    privateKey: string;
  }> {
    const fieldKey = await this.fieldCrypto.generateFieldKey(seed, context);
    
    const publicKey = ccmHash({
      field: fieldKey.field,
      holographic_correspondence: fieldKey.holographic_correspondence
    }, "public_key");
    
    const privateKey = ccmHash({
      fieldKey,
      seed,
      context
    }, "private_key");
    
    return { fieldKey, publicKey, privateKey };
  }

  /**
   * Encrypt data with quantum-resistant encryption
   */
  async encrypt(
    plaintext: number[][],
    fieldKey: import("./InformationFieldCrypto").FieldKey,
    context: unknown
  ): Promise<import("./ResonanceEncryption").ResonanceCiphertext> {
    return this.resonanceEncryption.encrypt(plaintext, fieldKey, context);
  }

  /**
   * Decrypt data with quantum-resistant decryption
   */
  async decrypt(
    ciphertext: import("./ResonanceEncryption").ResonanceCiphertext,
    fieldKey: import("./InformationFieldCrypto").FieldKey,
    context: unknown
  ): Promise<import("./ResonanceEncryption").ResonanceDecryptionResult> {
    return this.resonanceEncryption.decrypt(ciphertext, fieldKey, context);
  }

  /**
   * Create quantum-resistant signature
   */
  async sign(
    message: unknown,
    fieldKey: import("./InformationFieldCrypto").FieldKey
  ): Promise<import("./InformationFieldCrypto").CoherenceSignature> {
    return this.fieldCrypto.createCoherenceSignature(message, fieldKey);
  }

  /**
   * Verify quantum-resistant signature
   */
  async verify(
    message: unknown,
    signature: import("./InformationFieldCrypto").CoherenceSignature,
    fieldKey: import("./InformationFieldCrypto").FieldKey
  ): Promise<boolean> {
    return this.fieldCrypto.verifyCoherenceSignature(message, signature, fieldKey);
  }

  /**
   * Generate authentication challenge
   */
  async generateAuthChallenge(
    identity: string,
    context: unknown
  ): Promise<import("./ConservationBasedAuth").ConservationChallenge> {
    return this.conservationAuth.generateChallenge(identity, context);
  }

  /**
   * Verify authentication response
   */
  async verifyAuthResponse(
    response: import("./ConservationBasedAuth").ConservationResponse,
    identity: string,
    context: unknown
  ): Promise<import("./ConservationBasedAuth").ConservationAuthResult> {
    return this.conservationAuth.verifyResponse(response, identity, context);
  }

  /**
   * Verify session token
   */
  async verifySession(sessionToken: string): Promise<import("./ConservationBasedAuth").ConservationAuthResult | null> {
    return this.conservationAuth.verifySession(sessionToken);
  }

  /**
   * Get system statistics
   */
  getSystemStats(): {
    fieldCrypto: { size: number; hit_rate: number };
    resonanceEncryption: { size: number; hit_rate: number };
    conservationAuth: { active_challenges: number; active_sessions: number; cache_size: number };
  } {
    return {
      fieldCrypto: this.fieldCrypto.getCacheStats(),
      resonanceEncryption: this.resonanceEncryption.getCacheStats(),
      conservationAuth: this.conservationAuth.getStats()
    };
  }

  /**
   * Clear all caches
   */
  clearAllCaches(): void {
    this.fieldCrypto.clearCache();
    this.resonanceEncryption.clearCache();
    this.conservationAuth.cleanup();
  }
}

/**
 * Global quantum-resistant crypto system instance
 */
let globalQuantumCryptoSystemInstance: QuantumResistantCryptoSystem | null = null;

/**
 * Get or create global quantum-resistant crypto system instance
 */
export function getQuantumResistantCryptoSystem(
  config?: {
    fieldCrypto?: Partial<import("./InformationFieldCrypto").QuantumResistantConfig>;
    resonanceEncryption?: Partial<import("./ResonanceEncryption").ResonanceEncryptionConfig>;
    conservationAuth?: Partial<import("./ConservationBasedAuth").ConservationAuthConfig>;
  }
): QuantumResistantCryptoSystem {
  if (!globalQuantumCryptoSystemInstance) {
    globalQuantumCryptoSystemInstance = new QuantumResistantCryptoSystem(config);
  }
  return globalQuantumCryptoSystemInstance;
}

/**
 * Convenience functions for complete quantum-resistant operations
 */
export async function createQuantumResistantKeyPair(
  seed: string,
  context: unknown
): Promise<{
  fieldKey: import("./InformationFieldCrypto").FieldKey;
  publicKey: string;
  privateKey: string;
}> {
  const system = getQuantumResistantCryptoSystem();
  return system.generateKeyPair(seed, context);
}

export async function encryptQuantumResistant(
  plaintext: number[][],
  fieldKey: import("./InformationFieldCrypto").FieldKey,
  context: unknown
): Promise<import("./ResonanceEncryption").ResonanceCiphertext> {
  const system = getQuantumResistantCryptoSystem();
  return system.encrypt(plaintext, fieldKey, context);
}

export async function decryptQuantumResistant(
  ciphertext: import("./ResonanceEncryption").ResonanceCiphertext,
  fieldKey: import("./InformationFieldCrypto").FieldKey,
  context: unknown
): Promise<import("./ResonanceEncryption").ResonanceDecryptionResult> {
  const system = getQuantumResistantCryptoSystem();
  return system.decrypt(ciphertext, fieldKey, context);
}

export async function signQuantumResistant(
  message: unknown,
  fieldKey: import("./InformationFieldCrypto").FieldKey
): Promise<import("./InformationFieldCrypto").CoherenceSignature> {
  const system = getQuantumResistantCryptoSystem();
  return system.sign(message, fieldKey);
}

export async function verifyQuantumResistant(
  message: unknown,
  signature: import("./InformationFieldCrypto").CoherenceSignature,
  fieldKey: import("./InformationFieldCrypto").FieldKey
): Promise<boolean> {
  const system = getQuantumResistantCryptoSystem();
  return system.verify(message, signature, fieldKey);
}

export async function authenticateQuantumResistant(
  identity: string,
  context: unknown
): Promise<{
  challenge: import("./ConservationBasedAuth").ConservationChallenge;
  response: (solution: number[][]) => Promise<import("./ConservationBasedAuth").ConservationAuthResult>;
}> {
  const system = getQuantumResistantCryptoSystem();
  const challenge = await system.generateAuthChallenge(identity, context);
  
  const response = async (solution: number[][]) => {
    const conservationResponse: import("./ConservationBasedAuth").ConservationResponse = {
      response_id: ccmHash({ challenge: challenge.challenge_id, solution }, "response_id"),
      challenge_id: challenge.challenge_id,
      conservation_solution: solution,
      coherence_proof: ccmHash({ solution, requirement: challenge.coherence_requirement }, "coherence_proof"),
      holographic_verification: ccmHash({ solution, context: challenge.holographic_context }, "holographic_verification"),
      field_correspondence: ccmHash({ solution, topology: challenge.field_topology }, "field_correspondence"),
      timestamp: Date.now()
    };
    
    return system.verifyAuthResponse(conservationResponse, identity, context);
  };
  
  return { challenge, response };
}

/**
 * Utility functions for quantum-resistant operations
 */

/**
 * Convert data to field format for encryption
 */
export function dataToField(data: unknown): number[][] {
  // Validate input data before JSON conversion
  const validation = validateDataForJson(data);
  if (!validation.valid) {
    throw new Error(`Data validation failed: ${validation.issues.join(', ')}`);
  }

  // Use safe JSON stringify with error recovery
  const dataString = safeJsonStringify(data);

  const field: number[][] = [];
  
  // Convert string to 48x256 field
  for (let p = 0; p < P; p++) {
    const row: number[] = [];
    for (let c = 0; c < C; c++) {
      const charIndex = (p * C + c) % dataString.length;
      const charCode = dataString.charCodeAt(charIndex);
      
      // Validate char code range
      if (charCode < 0 || charCode > 255) {
        throw new Error(`Invalid character code ${charCode} at position ${charIndex}`);
      }
      
      row.push(charCode / 255.0); // Normalize to [0,1]
    }
    field.push(row);
  }
  
  return field;
}

/**
 * Convert field format back to data
 */
export function fieldToData(field: number[][]): unknown {
  // Validate field dimensions first
  if (!validateFieldDimensions(field)) {
    throw new Error("Invalid field dimensions - field must be P x C");
  }

  const charCodes: number[] = [];
  
  try {
    for (let p = 0; p < P; p++) {
      for (let c = 0; c < C; c++) {
        const normalizedValue = field[p][c];
        
        // Validate normalized value range
        if (typeof normalizedValue !== 'number' || isNaN(normalizedValue)) {
          throw new Error(`Invalid field value at position [${p}][${c}]: ${normalizedValue}`);
        }
        
        if (normalizedValue < 0 || normalizedValue > 1) {
          throw new Error(`Field value out of range [0,1] at position [${p}][${c}]: ${normalizedValue}`);
        }
        
        const charCode = Math.round(normalizedValue * 255);
        
        // Validate char code range
        if (charCode < 0 || charCode > 255) {
          throw new Error(`Invalid character code ${charCode} at position [${p}][${c}]`);
        }
        
        charCodes.push(charCode);
      }
    }
  } catch (error) {
    throw new Error(`Field to character code conversion failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
  }
  
  let dataString: string;
  try {
    dataString = String.fromCharCode(...charCodes);
  } catch (error) {
    throw new Error(`Character code to string conversion failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
  }
  
  // Validate data string before JSON parsing
  if (!dataString || dataString.length === 0) {
    throw new Error("Empty data string - cannot parse JSON");
  }
  
  // Use safe JSON parse with error recovery
  return safeJsonParse(dataString);
}

/**
 * Validate field dimensions
 */
export function validateFieldDimensions(field: number[][]): boolean {
  if (!Array.isArray(field)) return false;
  if (field.length !== P) return false;
  for (let p = 0; p < P; p++) {
    if (!Array.isArray(field[p]) || field[p].length !== C) return false;
  }
  return true;
}

/**
 * Safe JSON stringify with error recovery
 */
export function safeJsonStringify(data: unknown, fallback?: string): string {
  try {
    // Pre-validate data for common issues
    if (data === null || data === undefined) {
      return fallback || 'null';
    }
    
    if (typeof data === 'function') {
      throw new Error("Functions cannot be serialized to JSON");
    }
    
    const result = JSON.stringify(data);
    
    // Validate result size
    if (result.length > 1000000) {
      throw new Error("Serialized data too large");
    }
    
    return result;
  } catch (error) {
    if (fallback !== undefined) {
      return fallback;
    }
    
    // Attempt recovery strategies
    if (error instanceof TypeError && error.message.includes('circular')) {
      throw new Error("Circular reference detected - use a custom serializer or provide fallback");
    }
    
    // Try to serialize a simplified version
    try {
      const simplified = typeof data === 'object' ? { type: typeof data, keys: Object.keys(data || {}) } : String(data);
      return JSON.stringify(simplified);
    } catch {
      throw new Error(`JSON serialization failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }
}

/**
 * Safe JSON parse with error recovery
 */
export function safeJsonParse(jsonString: string, fallback?: unknown): unknown {
  try {
    if (!jsonString || typeof jsonString !== 'string') {
      throw new Error("Invalid input - expected non-empty string");
    }
    
    // Basic JSON syntax validation
    const trimmed = jsonString.trim();
    if (trimmed.length === 0) {
      throw new Error("Empty JSON string");
    }
    
    // Check for common JSON patterns
    if (!trimmed.startsWith('{') && !trimmed.startsWith('[') && !trimmed.startsWith('"') && 
        trimmed !== 'null' && trimmed !== 'true' && trimmed !== 'false' && 
        !/^-?\d/.test(trimmed)) {
      throw new Error("Invalid JSON format");
    }
    
    return JSON.parse(jsonString);
  } catch (error) {
    if (fallback !== undefined) {
      return fallback;
    }
    
    // Attempt recovery strategies
    if (error instanceof SyntaxError) {
      // Try to fix common JSON issues
      try {
        const fixed = jsonString
          .replace(/([{,]\s*)(\w+):/g, '$1"$2":') // Add quotes to unquoted keys
          .replace(/:\s*([^",{\[\s][^,}\]\s]*)/g, ': "$1"') // Add quotes to unquoted string values
          .replace(/'/g, '"'); // Replace single quotes with double quotes
        
        if (fixed !== jsonString) {
          return JSON.parse(fixed);
        }
      } catch {
        // Recovery failed, throw original error
      }
      
      throw new Error(`JSON parsing failed - invalid syntax: ${error.message}`);
    }
    
    throw new Error(`JSON parsing failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
  }
}

/**
 * Validate data for JSON serialization compatibility
 */
export function validateDataForJson(data: unknown): { valid: boolean; issues: string[] } {
  const issues: string[] = [];
  
  if (data === null || data === undefined) {
    return { valid: true, issues: [] };
  }
  
  if (typeof data === 'function') {
    issues.push("Functions cannot be serialized to JSON");
  }
  
  if (typeof data === 'symbol') {
    issues.push("Symbols cannot be serialized to JSON");
  }
  
  if (typeof data === 'bigint') {
    issues.push("BigInt values cannot be serialized to JSON");
  }
  
  // Check for circular references (basic check)
  if (typeof data === 'object') {
    try {
      JSON.stringify(data);
    } catch (error) {
      if (error instanceof TypeError && error.message.includes('circular')) {
        issues.push("Circular reference detected");
      }
    }
  }
  
  return { valid: issues.length === 0, issues };
}

/**
 * Sanitize input data for safe processing
 */
export function sanitizeInputData(data: unknown): unknown {
  if (data === null || data === undefined) {
    return data;
  }
  
  if (typeof data === 'string') {
    // Remove potentially dangerous characters and normalize
    return data
      .replace(/[\x00-\x1F\x7F-\x9F]/g, '') // Remove control characters
      .trim();
  }
  
  if (typeof data === 'number') {
    // Validate number range and handle special values
    if (!isFinite(data)) {
      throw new Error("Invalid number: must be finite");
    }
    return data;
  }
  
  if (typeof data === 'boolean') {
    return data;
  }
  
  if (Array.isArray(data)) {
    // Recursively sanitize array elements
    return data.map(item => sanitizeInputData(item));
  }
  
  if (typeof data === 'object') {
    // Sanitize object properties
    const sanitized: Record<string, unknown> = {};
    for (const [key, value] of Object.entries(data)) {
      // Sanitize key
      const sanitizedKey = key.replace(/[^a-zA-Z0-9_]/g, '_');
      sanitized[sanitizedKey] = sanitizeInputData(value);
    }
    return sanitized;
  }
  
  // For other types, convert to string and sanitize
  return sanitizeInputData(String(data));
}

/**
 * Type-safe data conversion with validation
 */
export function convertDataSafely<T>(data: unknown, expectedType: string): T {
  const sanitized = sanitizeInputData(data);
  
  switch (expectedType) {
    case 'string':
      if (typeof sanitized === 'string') return sanitized as T;
      return String(sanitized) as T;
      
    case 'number':
      if (typeof sanitized === 'number') return sanitized as T;
      const num = Number(sanitized);
      if (isNaN(num)) throw new Error(`Cannot convert to number: ${sanitized}`);
      return num as T;
      
    case 'boolean':
      if (typeof sanitized === 'boolean') return sanitized as T;
      if (typeof sanitized === 'string') {
        const lower = sanitized.toLowerCase();
        if (lower === 'true') return true as T;
        if (lower === 'false') return false as T;
      }
      return Boolean(sanitized) as T;
      
    case 'object':
      if (typeof sanitized === 'object' && sanitized !== null) return sanitized as T;
      throw new Error(`Expected object, got ${typeof sanitized}`);
      
    case 'array':
      if (Array.isArray(sanitized)) return sanitized as T;
      throw new Error(`Expected array, got ${typeof sanitized}`);
      
    default:
      return sanitized as T;
  }
}

/**
 * Create test field for validation
 */
export function createTestField(): number[][] {
  const field: number[][] = [];
  
  for (let p = 0; p < P; p++) {
    const row: number[] = [];
    for (let c = 0; c < C; c++) {
      // Create test pattern that maintains conservation
      const value = Math.sin((p * C + c) * Math.PI / N) * 0.5;
      row.push(value);
    }
    field.push(row);
  }
  
  return field;
}

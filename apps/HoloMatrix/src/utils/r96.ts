/**
 * Centralized R96 Hash Generation Utility
 * 
 * This module provides a consistent R96 hash generation implementation
 * that matches the real Hologram SDK to prevent witness verification mismatches.
 */

import { ccmHash } from '../../../../libs/sdk/node/sdk/dist/index.js';

/**
 * Generate a deterministic 24-hex checksum from bytes (R96) using SDK
 * This matches the real SDK implementation to ensure witness consistency
 */
export function generateR96(bytes: Buffer): string {
  return ccmHash(bytes, 'r96').slice(0, 24);
}

/**
 * Legacy 8-character R96 generation for backward compatibility
 * Only use this for test scenarios where 8-char format is expected
 */
export function generateR96Legacy(bytes: Buffer): string {
  let hash = 0;
  for (let i = 0; i < bytes.length; i++) {
    hash = ((hash << 5) - hash + bytes[i]) & 0xffffffff;
  }
  return Math.abs(hash).toString(16).padStart(8, '0');
}

/**
 * Verify R96 hash consistency between two implementations
 */
export function verifyR96Consistency(bytes: Buffer): {
  sdkR96: string;
  legacyR96: string;
  consistent: boolean;
} {
  const sdkR96 = generateR96(bytes);
  const legacyR96 = generateR96Legacy(bytes);
  
  return {
    sdkR96,
    legacyR96,
    consistent: sdkR96.slice(0, 8) === legacyR96 // Check if first 8 chars match
  };
}

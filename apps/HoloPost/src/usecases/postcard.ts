/**
 * HoloPost Use Case - Postcard Message System
 * 
 * This module implements the core use case: sending a "postcard" message
 * across the Hologram lattice, storing it with proofs, and processing it
 * with a kernel that "stamps" it.
 */

import { Postcard, Budget } from '../types';
import { uorIdFromBytes, place } from '../adapters/hologram';
import { mkWitness, mkPostcard, logPlacement } from '../testkit';

/**
 * Create a postcard with all necessary metadata
 */
export function createPostcard(
  message: string,
  from: string = 'Alice',
  to: string = 'Bob'
): Postcard {
  const data = mkPostcard(message, from, to);
  const id = uorIdFromBytes(data.bytes);
  
  return {
    id,
    message: data.message,
    from: data.from,
    to: data.to,
    timestamp: data.timestamp,
    bytes: data.bytes,
  };
}

/**
 * Get placement information for a postcard
 */
export function getPostcardPlacement(postcard: Postcard): Array<{ r: number; c: number }> {
  const placements = place(postcard.id, { rows: 48, cols: 256, parity: 2 });
  logPlacement(postcard.id, placements);
  return placements;
}

/**
 * Create a witness for a postcard
 */
export async function createPostcardWitness(postcard: Postcard): Promise<{
  r96: string;
  probes: number;
  timestamp: number;
}> {
  return await mkWitness(postcard.bytes);
}

/**
 * Validate a postcard's integrity
 */
export async function validatePostcard(postcard: Postcard): Promise<boolean> {
  try {
    // Verify the ID matches the content
    const expectedId = uorIdFromBytes(postcard.bytes);
    if (postcard.id !== expectedId) {
      console.error(`❌ Postcard ID mismatch: expected ${expectedId}, got ${postcard.id}`);
      return false;
    }
    
    // Verify the content is valid JSON
    const parsed = JSON.parse(postcard.bytes.toString('utf8'));
    if (parsed.message !== postcard.message || 
        parsed.from !== postcard.from || 
        parsed.to !== postcard.to) {
      console.error('❌ Postcard content mismatch');
      return false;
    }
    
    console.log('✅ Postcard validation passed');
    return true;
  } catch (error) {
    console.error('❌ Postcard validation failed:', error);
    return false;
  }
}

/**
 * Create a budget for postcard operations
 */
export function createPostcardBudget(): Budget {
  return {
    io: 500,      // I/O operations
    cpuMs: 50,    // CPU time in milliseconds
    mem: 32,      // Memory in MB
  };
}

/**
 * Log postcard information
 */
export function logPostcard(postcard: Postcard): void {
  console.log('📮 Postcard Details:');
  console.log(`   ID: ${postcard.id.substring(0, 16)}...`);
  console.log(`   From: ${postcard.from}`);
  console.log(`   To: ${postcard.to}`);
  console.log(`   Message: "${postcard.message}"`);
  console.log(`   Size: ${postcard.bytes.length} bytes`);
  console.log(`   Timestamp: ${new Date(postcard.timestamp).toISOString()}`);
}

/**
 * Create a sample postcard for testing
 */
export function createSamplePostcard(): Postcard {
  const messages = [
    'Hello from the Hologram lattice! 🌟',
    'Wish you were here in virtual space! 🚀',
    'Greetings from the 12,288-cell network! ⚡',
    'Sending love through quantum channels! 💫',
    'Hope this finds you well in the metaverse! 🌈',
  ];
  
  const message = messages[Math.floor(Math.random() * messages.length)];
  return createPostcard(message || 'Hello from the hologram!', 'HoloUser', 'Friend');
}

/**
 * Create multiple postcards for batch testing
 */
export function createBatchPostcards(count: number): Postcard[] {
  const postcards: Postcard[] = [];
  
  for (let i = 0; i < count; i++) {
    const message = `Batch message #${i + 1} from the Hologram lattice`;
    const from = `User${i + 1}`;
    const to = `Recipient${i + 1}`;
    postcards.push(createPostcard(message, from, to));
  }
  
  return postcards;
}

/**
 * Compare two postcards for equality
 */
export function comparePostcards(a: Postcard, b: Postcard): boolean {
  return (
    a.id === b.id &&
    a.message === b.message &&
    a.from === b.from &&
    a.to === b.to &&
    a.timestamp === b.timestamp &&
    a.bytes.equals(b.bytes)
  );
}

/**
 * Extract postcard metadata for logging
 */
export function getPostcardMetadata(postcard: Postcard): {
  id: string;
  size: number;
  from: string;
  to: string;
  messageLength: number;
  timestamp: string;
} {
  return {
    id: postcard.id,
    size: postcard.bytes.length,
    from: postcard.from,
    to: postcard.to,
    messageLength: postcard.message.length,
    timestamp: new Date(postcard.timestamp).toISOString(),
  };
}

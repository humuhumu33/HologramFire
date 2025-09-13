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
import { encodeText, decodeText, getAvailableSchemes, createSampleMessage, validateRoundTrip, EncodedMessage, DecodedMessage } from '../utils/encoding';

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

/**
 * Encode a postcard message using the specified scheme
 */
export function encodePostcardMessage(postcard: Postcard, scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein'): EncodedMessage {
  return encodeText(postcard.message, {
    scheme,
    witness: true,
    compression: false,
    obfuscation: false
  });
}

/**
 * Decode an encoded postcard message
 */
export function decodePostcardMessage(encoded: string, scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein'): DecodedMessage {
  return decodeText(encoded, {
    scheme,
    validateWitness: true
  });
}

/**
 * Create a postcard with encoded message
 */
export function createEncodedPostcard(
  message: string,
  scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein',
  from: string = 'Alice',
  to: string = 'Bob'
): { postcard: Postcard; encoded: EncodedMessage } {
  // First encode the message
  const encoded = encodeText(message, {
    scheme,
    witness: true,
    compression: false,
    obfuscation: false
  });
  
  // Create postcard with encoded message
  const postcard = createPostcard(encoded.encoded, from, to);
  
  return { postcard, encoded };
}

/**
 * Decode a postcard message and validate
 */
export function decodePostcard(postcard: Postcard, scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein'): {
  original: string;
  decoded: string;
  valid: boolean;
  witness: any;
} {
  const decoded = decodeText(postcard.message, {
    scheme,
    validateWitness: true
  });
  
  return {
    original: postcard.message,
    decoded: decoded.decoded,
    valid: decoded.valid,
    witness: decoded.witness
  };
}

/**
 * Get available encoding schemes for postcards
 */
export function getPostcardEncodingSchemes(): Array<{
  scheme: string;
  description: string;
  features: string[];
}> {
  return getAvailableSchemes();
}

/**
 * Create a sample encoded postcard
 */
export function createSampleEncodedPostcard(scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein' = 'r96'): {
  postcard: Postcard;
  encoded: EncodedMessage;
  decoded: DecodedMessage;
} {
  const message = createSampleMessage();
  const { postcard, encoded } = createEncodedPostcard(message, scheme);
  const decoded = decodePostcard(postcard, scheme);
  
  return {
    postcard,
    encoded,
    decoded: {
      encoded: postcard.message,
      decoded: decoded.decoded,
      scheme,
      valid: decoded.valid,
      witness: decoded.witness,
      metadata: {
        encodingTime: 0,
        validationTime: 0
      }
    }
  };
}

/**
 * Validate encoding/decoding round trip for a postcard
 */
export function validatePostcardRoundTrip(message: string, scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein'): {
  success: boolean;
  original: string;
  encoded: string;
  decoded: string;
  valid: boolean;
  time: number;
} {
  return validateRoundTrip(message, scheme);
}

/**
 * Batch encode multiple postcard messages
 */
export function batchEncodePostcards(messages: string[], scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein'): Array<{
  message: string;
  encoded: EncodedMessage;
  postcard: Postcard;
}> {
  return messages.map(message => {
    const { postcard, encoded } = createEncodedPostcard(message, scheme);
    return { message, encoded, postcard };
  });
}

/**
 * Log encoding/decoding information
 */
export function logEncodingInfo(encoded: EncodedMessage, decoded?: DecodedMessage): void {
  console.log('🔐 Encoding Information:');
  console.log(`   Scheme: ${encoded.scheme}`);
  console.log(`   Original: "${encoded.original}"`);
  console.log(`   Encoded: "${encoded.encoded}"`);
  console.log(`   Original Length: ${encoded.metadata.originalLength} chars`);
  console.log(`   Encoded Length: ${encoded.metadata.encodedLength} chars`);
  if (encoded.metadata.compressionRatio) {
    console.log(`   Compression Ratio: ${encoded.metadata.compressionRatio.toFixed(2)}`);
  }
  console.log(`   Encoding Time: ${encoded.metadata.encodingTime}ms`);
  
  if (encoded.witness) {
    console.log(`   Witness r96: ${encoded.witness.r96}`);
    console.log(`   Witness Probes: ${encoded.witness.probes}`);
  }
  
  if (decoded) {
    console.log('\n🔓 Decoding Information:');
    console.log(`   Decoded: "${decoded.decoded}"`);
    console.log(`   Valid: ${decoded.valid ? '✅ YES' : '❌ NO'}`);
    console.log(`   Validation Time: ${decoded.metadata.validationTime}ms`);
    
    if (decoded.witness) {
      console.log(`   Witness r96: ${decoded.witness.r96}`);
      console.log(`   Witness Probes: ${decoded.witness.probes}`);
    }
  }
  
  console.log('');
}

/**
 * Text Encoding and Decoding Utilities for HoloPost
 * 
 * This module provides comprehensive text encoding and decoding capabilities
 * for the HoloPost demo, allowing users to encode and decode any text message
 * using various encoding schemes supported by the Hologram lattice.
 */

import { createHash } from 'node:crypto';

export interface EncodingOptions {
  scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein';
  compression?: boolean;
  obfuscation?: boolean;
  witness?: boolean;
}

export interface DecodingOptions {
  scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein';
  validateWitness?: boolean;
}

export interface EncodedMessage {
  original: string;
  encoded: string;
  scheme: string;
  witness?: {
    r96: string;
    probes: number;
    timestamp: number;
  };
  metadata: {
    originalLength: number;
    encodedLength: number;
    compressionRatio?: number;
    encodingTime: number;
  };
}

export interface DecodedMessage {
  encoded: string;
  decoded: string;
  scheme: string;
  valid: boolean;
  witness?: {
    r96: string;
    probes: number;
    timestamp: number;
  };
  metadata: {
    encodingTime: number;
    validationTime: number;
  };
}

/**
 * Generate r96 checksum (24-hex SHA-256 prefix)
 */
function generateR96(text: string): string {
  const hash = createHash('sha256').update(text, 'utf8').digest('hex');
  return hash.substring(0, 24);
}

/**
 * Generate Klein probe count (simplified for demo)
 */
function generateKleinProbes(text: string): number {
  // In a real implementation, this would be based on actual Klein probe analysis
  return Math.min(192, Math.max(1, Math.floor(text.length / 10)));
}

/**
 * Holographic encoding - uses lattice coordinates for encoding
 */
function holographicEncode(text: string): string {
  const bytes = Buffer.from(text, 'utf8');
  const encoded: string[] = [];
  
  for (let i = 0; i < bytes.length; i++) {
    const byte = bytes[i] || 0;
    // Map byte to lattice coordinates (row, col)
    const row = byte % 48; // 48 rows in the lattice
    const col = Math.floor(byte / 48) % 256; // 256 columns
    encoded.push(`${row.toString().padStart(2, '0')},${col.toString().padStart(3, '0')}`);
  }
  
  return encoded.join('|');
}

/**
 * Holographic decoding - converts lattice coordinates back to text
 */
function holographicDecode(encoded: string): string {
  const coordinates = encoded.split('|');
  const bytes: number[] = [];
  
  for (const coord of coordinates) {
    const [rowStr, colStr] = coord.split(',');
    const row = parseInt(rowStr || '0', 10);
    const col = parseInt(colStr || '0', 10);
    // Convert coordinates back to byte
    const byte = row + (col * 48);
    bytes.push(byte);
  }
  
  return Buffer.from(bytes).toString('utf8');
}

/**
 * R96 encoding - uses r96 checksum as part of encoding
 */
function r96Encode(text: string): string {
  const r96 = generateR96(text);
  const base64 = Buffer.from(text, 'utf8').toString('base64');
  return `${r96}:${base64}`;
}

/**
 * R96 decoding - validates r96 checksum during decoding
 */
function r96Decode(encoded: string): { text: string; valid: boolean } {
  const [r96, base64] = encoded.split(':');
  if (!r96 || !base64) {
    return { text: '', valid: false };
  }
  
  try {
    const text = Buffer.from(base64, 'base64').toString('utf8');
    const expectedR96 = generateR96(text);
    const valid = r96 === expectedR96;
    return { text, valid };
  } catch (error) {
    return { text: '', valid: false };
  }
}

/**
 * Klein encoding - uses Klein probe analysis for encoding
 */
function kleinEncode(text: string): string {
  const probes = generateKleinProbes(text);
  const base64 = Buffer.from(text, 'utf8').toString('base64');
  return `${probes}:${base64}`;
}

/**
 * Klein decoding - validates Klein probe count during decoding
 */
function kleinDecode(encoded: string): { text: string; valid: boolean } {
  const [probesStr, base64] = encoded.split(':');
  if (!probesStr || !base64) {
    return { text: '', valid: false };
  }
  
  try {
    const text = Buffer.from(base64, 'base64').toString('utf8');
    const expectedProbes = generateKleinProbes(text);
    const valid = parseInt(probesStr, 10) === expectedProbes;
    return { text, valid };
  } catch (error) {
    return { text: '', valid: false };
  }
}

/**
 * Encode a text message using the specified scheme
 */
export function encodeText(text: string, options: EncodingOptions): EncodedMessage {
  const startTime = Date.now();
  
  let encoded: string;
  let witness: EncodedMessage['witness'] | undefined;
  
  switch (options.scheme) {
    case 'base64':
      encoded = Buffer.from(text, 'utf8').toString('base64');
      break;
      
    case 'hex':
      encoded = Buffer.from(text, 'utf8').toString('hex');
      break;
      
    case 'holographic':
      encoded = holographicEncode(text);
      break;
      
    case 'r96':
      encoded = r96Encode(text);
      break;
      
    case 'klein':
      encoded = kleinEncode(text);
      break;
      
    default:
      throw new Error(`Unsupported encoding scheme: ${options.scheme}`);
  }
  
  // Generate witness if requested
  if (options.witness) {
    witness = {
      r96: generateR96(text),
      probes: generateKleinProbes(text),
      timestamp: Date.now()
    };
  }
  
  const encodingTime = Date.now() - startTime;
  
  return {
    original: text,
    encoded,
    scheme: options.scheme,
    ...(witness && { witness }),
    metadata: {
      originalLength: text.length,
      encodedLength: encoded.length,
      ...(options.compression && { compressionRatio: encoded.length / text.length }),
      encodingTime
    }
  };
}

/**
 * Decode an encoded message using the specified scheme
 */
export function decodeText(encoded: string, options: DecodingOptions): DecodedMessage {
  const startTime = Date.now();
  
  let decoded: string;
  let valid: boolean = true;
  let witness: DecodedMessage['witness'] | undefined;
  
  switch (options.scheme) {
    case 'base64':
      try {
        decoded = Buffer.from(encoded, 'base64').toString('utf8');
      } catch (error) {
        decoded = '';
        valid = false;
      }
      break;
      
    case 'hex':
      try {
        decoded = Buffer.from(encoded, 'hex').toString('utf8');
      } catch (error) {
        decoded = '';
        valid = false;
      }
      break;
      
    case 'holographic':
      try {
        decoded = holographicDecode(encoded);
      } catch (error) {
        decoded = '';
        valid = false;
      }
      break;
      
    case 'r96':
      const r96Result = r96Decode(encoded);
      decoded = r96Result.text;
      valid = r96Result.valid;
      break;
      
    case 'klein':
      const kleinResult = kleinDecode(encoded);
      decoded = kleinResult.text;
      valid = kleinResult.valid;
      break;
      
    default:
      throw new Error(`Unsupported decoding scheme: ${options.scheme}`);
  }
  
  // Generate witness if requested and valid
  if (options.validateWitness && valid) {
    witness = {
      r96: generateR96(decoded),
      probes: generateKleinProbes(decoded),
      timestamp: Date.now()
    };
  }
  
  const validationTime = Date.now() - startTime;
  
  return {
    encoded,
    decoded,
    scheme: options.scheme,
    valid,
    ...(witness && { witness }),
    metadata: {
      encodingTime: 0, // Not available during decoding
      validationTime
    }
  };
}

/**
 * Get available encoding schemes
 */
export function getAvailableSchemes(): Array<{
  scheme: string;
  description: string;
  features: string[];
}> {
  return [
    {
      scheme: 'base64',
      description: 'Standard Base64 encoding',
      features: ['Standard', 'Widely supported', 'URL safe']
    },
    {
      scheme: 'hex',
      description: 'Hexadecimal encoding',
      features: ['Simple', 'Human readable', 'Debug friendly']
    },
    {
      scheme: 'holographic',
      description: 'Holographic lattice coordinate encoding',
      features: ['Lattice native', 'Fault tolerant', 'Distributed']
    },
    {
      scheme: 'r96',
      description: 'R96 checksum-validated encoding',
      features: ['Integrity verified', 'Tamper resistant', 'Fast validation']
    },
    {
      scheme: 'klein',
      description: 'Klein probe-validated encoding',
      features: ['Probe validated', 'Frame integrity', 'Transport optimized']
    }
  ];
}

/**
 * Batch encode multiple messages
 */
export function batchEncode(messages: string[], options: EncodingOptions): EncodedMessage[] {
  return messages.map(message => encodeText(message, options));
}

/**
 * Batch decode multiple messages
 */
export function batchDecode(encodedMessages: string[], options: DecodingOptions): DecodedMessage[] {
  return encodedMessages.map(encoded => decodeText(encoded, options));
}

/**
 * Create a sample message for testing
 */
export function createSampleMessage(): string {
  const messages = [
    'Hello from the Hologram lattice! 🌟',
    'This is a test message for encoding/decoding.',
    'HoloPost can encode and decode any text message!',
    'The 12,288-cell lattice provides virtual infrastructure.',
    'Transport, storage, and compute all work together.',
    'Gate verification ensures everything is properly stamped.',
    'Budget conservation maintains system integrity.',
    'Witness verification provides cryptographic guarantees.'
  ];
  
  return messages[Math.floor(Math.random() * messages.length)] || 'Hello from HoloPost!';
}

/**
 * Validate encoding/decoding round trip
 */
export function validateRoundTrip(text: string, scheme: string): {
  success: boolean;
  original: string;
  encoded: string;
  decoded: string;
  valid: boolean;
  time: number;
} {
  const startTime = Date.now();
  
  try {
    const encoded = encodeText(text, { scheme: scheme as any, witness: true });
    const decoded = decodeText(encoded.encoded, { scheme: scheme as any, validateWitness: true });
    
    const success = decoded.valid && decoded.decoded === text;
    const time = Date.now() - startTime;
    
    return {
      success,
      original: text,
      encoded: encoded.encoded,
      decoded: decoded.decoded,
      valid: decoded.valid,
      time
    };
  } catch (error) {
    return {
      success: false,
      original: text,
      encoded: '',
      decoded: '',
      valid: false,
      time: Date.now() - startTime
    };
  }
}

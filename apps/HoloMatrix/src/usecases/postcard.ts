/**
 * Postcard use case - Simple text payload for baseline testing
 * Provides a lightweight test case for transport and storage verification
 */

import type { Budget, Witness } from '../types';
import { uorIdFromBytes, mkWitness } from '../testkit';

export interface PostcardPayload {
  id: string;
  content: string;
  timestamp: number;
  sender: string;
  recipient: string;
}

export class PostcardUseCase {
  private payloads: PostcardPayload[] = [];

  /**
   * Create a postcard payload
   */
  createPostcard(content: string, sender: string, recipient: string): PostcardPayload {
    const payload: PostcardPayload = {
      id: `postcard-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      content,
      timestamp: Date.now(),
      sender,
      recipient
    };

    this.payloads.push(payload);
    return payload;
  }

  /**
   * Serialize postcard to buffer
   */
  serializePostcard(postcard: PostcardPayload): Buffer {
    const json = JSON.stringify(postcard);
    return Buffer.from(json, 'utf8');
  }

  /**
   * Deserialize buffer to postcard
   */
  deserializePostcard(buffer: Buffer): PostcardPayload {
    const json = buffer.toString('utf8');
    return JSON.parse(json);
  }

  /**
   * Generate UOR ID for postcard
   */
  getUorId(postcard: PostcardPayload): string {
    const buffer = this.serializePostcard(postcard);
    return uorIdFromBytes(buffer);
  }

  /**
   * Create witness for postcard
   */
  createWitness(postcard: PostcardPayload): Witness {
    const buffer = this.serializePostcard(postcard);
    const r96 = this.generateR96(buffer);
    return mkWitness(r96);
  }

  /**
   * Generate R96 hash for buffer
   */
  private generateR96(buffer: Buffer): string {
    // Simple hash for testing
    let hash = 0;
    for (let i = 0; i < buffer.length; i++) {
      hash = ((hash << 5) - hash + buffer[i]) & 0xffffffff;
    }
    return Math.abs(hash).toString(16).padStart(8, '0');
  }

  /**
   * Create budget for postcard operations
   */
  createBudget(): Budget {
    return {
      cpuMs: 10,  // 10ms CPU
      io: 1,      // 1 IO operation
      mem: 1024   // 1KB memory
    };
  }

  /**
   * Get all created postcards
   */
  getAllPostcards(): PostcardPayload[] {
    return [...this.payloads];
  }

  /**
   * Clear all postcards
   */
  clear(): void {
    this.payloads = [];
  }

  /**
   * Create a batch of test postcards
   */
  createTestBatch(count: number): PostcardPayload[] {
    const postcards: PostcardPayload[] = [];
    
    for (let i = 0; i < count; i++) {
      const postcard = this.createPostcard(
        `Test message ${i + 1} - Hello from Hologram!`,
        `sender-${i % 10}`,
        `recipient-${i % 5}`
      );
      postcards.push(postcard);
    }
    
    return postcards;
  }

  /**
   * Validate postcard structure
   */
  validatePostcard(postcard: PostcardPayload): boolean {
    return !!(
      postcard.id &&
      postcard.content &&
      postcard.timestamp &&
      postcard.sender &&
      postcard.recipient &&
      typeof postcard.id === 'string' &&
      typeof postcard.content === 'string' &&
      typeof postcard.timestamp === 'number' &&
      typeof postcard.sender === 'string' &&
      typeof postcard.recipient === 'string'
    );
  }

  /**
   * Get postcard statistics
   */
  getStats(): {
    total: number;
    totalSize: number;
    averageSize: number;
    uniqueSenders: number;
    uniqueRecipients: number;
  } {
    const total = this.payloads.length;
    const totalSize = this.payloads.reduce((sum, p) => sum + this.serializePostcard(p).length, 0);
    const averageSize = total > 0 ? totalSize / total : 0;
    const uniqueSenders = new Set(this.payloads.map(p => p.sender)).size;
    const uniqueRecipients = new Set(this.payloads.map(p => p.recipient)).size;

    return {
      total,
      totalSize,
      averageSize,
      uniqueSenders,
      uniqueRecipients
    };
  }
}

/**
 * Create a postcard use case instance
 */
export function createPostcardUseCase(): PostcardUseCase {
  return new PostcardUseCase();
}

/**
 * Quick postcard creation utility
 */
export function createQuickPostcard(content: string): { payload: PostcardPayload; buffer: Buffer; uorId: string; witness: Witness } {
  const useCase = new PostcardUseCase();
  const payload = useCase.createPostcard(content, 'quick-sender', 'quick-recipient');
  const buffer = useCase.serializePostcard(payload);
  const uorId = useCase.getUorId(payload);
  const witness = useCase.createWitness(payload);
  
  return { payload, buffer, uorId, witness };
}

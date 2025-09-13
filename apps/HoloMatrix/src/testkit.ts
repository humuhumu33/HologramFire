/**
 * Testkit - Helper functions for testing and demo setup
 * Provides utilities for creating verifiers, CTP, storage, and budget management
 */

import type {
  Verifier,
  CTP,
  Storage,
  Budget,
  Receipt,
  HologramAdapter,
  LatticeCoord
} from './types';
import adapter from './adapters/hologram';

/**
 * Create a verifier instance
 */
export async function mkVerifier(): Promise<Verifier> {
  return await adapter.createVerifier();
}

/**
 * Create a CTP (Consensus Transport Protocol) instance
 */
export async function mkCTP(opts: {
  nodeId: string;
  lanes: number;
  windowMs: number;
}): Promise<CTP> {
  return await adapter.createCTP(opts);
}

/**
 * Create a storage instance
 */
export async function mkStorage(opts: {
  rows: 48;
  cols: 256;
  tileCols: number;
  ec: { k: number; m: number };
}): Promise<Storage> {
  return await adapter.createStorage(opts);
}

/**
 * Create a budget with specified resources
 */
export function budget(cpuMs: number = 1000, io: number = 1000, mem: number = 1000): Budget {
  return { cpuMs, io, mem };
}

/**
 * Create a zero budget
 */
export function zeroBudget(): Budget {
  return { cpuMs: 0, io: 0, mem: 0 };
}

/**
 * Assert that a receipt is closed
 */
export function assertClosed(receipt: Receipt, gate?: string): void {
  if (!receipt.closed) {
    throw new Error(`Receipt ${receipt.id} is not closed`);
  }
  if (gate && receipt.gate !== gate) {
    throw new Error(`Receipt ${receipt.id} gate mismatch: expected ${gate}, got ${receipt.gate}`);
  }
}

/**
 * Create a mock witness for testing
 */
export function mkWitness(r96: string, nodeId: string = 'test-node'): {
  r96: string;
  timestamp: number;
  nodeId: string;
} {
  return {
    r96,
    timestamp: Date.now(),
    nodeId
  };
}

/**
 * Generate a deterministic UOR ID from bytes
 */
export function uorIdFromBytes(bytes: Buffer): string {
  return adapter.uorIdFromBytes(bytes);
}

/**
 * Place data on the lattice
 */
export function place(id: string, opts: { rows: 48; cols: 256; parity?: number }): LatticeCoord[] {
  return adapter.place(id, opts);
}

/**
 * Validate lattice coordinates
 */
export function validateCoords(coords: LatticeCoord[]): void {
  if (coords.length < 3) {
    throw new Error(`Insufficient coordinates: need at least 3, got ${coords.length}`);
  }

  const usedRows = new Set<number>();
  for (const coord of coords) {
    if (coord.r < 0 || coord.r >= 48) {
      throw new Error(`Invalid row: ${coord.r} (must be 0-47)`);
    }
    if (coord.c < 0 || coord.c >= 256) {
      throw new Error(`Invalid column: ${coord.c} (must be 0-255)`);
    }
    usedRows.add(coord.r);
  }

  if (usedRows.size < 2) {
    throw new Error(`Insufficient row diversity: need at least 2 distinct rows, got ${usedRows.size}`);
  }
}

/**
 * Create a test matrix block
 */
export function mkMatrixBlock(size: number, fill: number = 1): Buffer {
  const data = new Int16Array(size * size);
  for (let i = 0; i < data.length; i++) {
    data[i] = fill;
  }
  return Buffer.from(data.buffer);
}

/**
 * Measure execution time
 */
export async function measureTime<T>(fn: () => Promise<T>): Promise<{ result: T; duration: number }> {
  const start = Date.now();
  const result = await fn();
  const duration = Date.now() - start;
  return { result, duration };
}

/**
 * Create a mock transport frame
 */
export function mkTransportFrame(lane: number, payload: Buffer, windowId: string): {
  lane: number;
  payload: Buffer;
  windowId: string;
  r96: string;
  timestamp: number;
} {
  const verifier = adapter.createVerifier();
  return {
    lane,
    payload,
    windowId,
    r96: 'mock-r96-hash',
    timestamp: Date.now()
  };
}

/**
 * Validate budget operations
 */
export function validateBudget(b: Budget): void {
  if (b.cpuMs < 0 || b.io < 0 || b.mem < 0) {
    throw new Error(`Invalid budget: negative values not allowed`);
  }
}

/**
 * Check if budget has sufficient resources
 */
export function hasBudget(b: Budget, required: Budget): boolean {
  return b.cpuMs >= required.cpuMs && b.io >= required.io && b.mem >= required.mem;
}

/**
 * Create a test storage policy
 */
export function mkStoragePolicy(replicas: number = 3, parity: number = 1): unknown {
  return {
    replicas,
    parity,
    faultDomains: Math.max(2, replicas - 1),
    ec: { k: replicas, m: parity }
  };
}

/**
 * Generate test data of specified size
 */
export function mkTestData(size: number, pattern: string = 'test'): Buffer {
  const data = Buffer.alloc(size);
  for (let i = 0; i < size; i++) {
    data[i] = pattern.charCodeAt(i % pattern.length);
  }
  return data;
}

/**
 * Create a mock compute kernel configuration
 */
export function mkComputeKernel(
  name: string,
  inputs: Array<{ id: string }>,
  budget: Budget
): {
  name: string;
  inputs: Array<{ id: string }>;
  budget: Budget;
  pin?: { near?: string; lane?: number };
  iopolicy?: { lane?: number; windowMs?: number };
} {
  return {
    name,
    inputs,
    budget,
    pin: { near: 'data', lane: 0 },
    iopolicy: { lane: 0, windowMs: 100 }
  };
}

/**
 * Wait for a specified duration
 */
export function sleep(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}

/**
 * Create a test node ID
 */
export function mkNodeId(prefix: string = 'test'): string {
  return `${prefix}-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
}

/**
 * Validate receipt structure
 */
export function validateReceipt(receipt: Receipt): void {
  if (!receipt.id || typeof receipt.id !== 'string') {
    throw new Error('Receipt must have a valid string ID');
  }
  if (typeof receipt.closed !== 'boolean') {
    throw new Error('Receipt closed field must be boolean');
  }
  if (typeof receipt.timestamp !== 'number' || receipt.timestamp <= 0) {
    throw new Error('Receipt must have a valid positive timestamp');
  }
  if (!receipt.gate || typeof receipt.gate !== 'string') {
    throw new Error('Receipt must have a valid gate name');
  }
}

/**
 * Create a test adapter instance
 */
export function mkAdapter(): HologramAdapter {
  return adapter;
}

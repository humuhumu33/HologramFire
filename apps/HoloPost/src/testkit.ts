/**
 * Test Kit - Helper functions for testing and demo
 * 
 * This module provides utility functions for creating test data,
 * verifying receipts, and asserting expected behaviors.
 */

import { Budget, Witness, Receipt, Placement } from './types';
import { createVerifier, createCTP, createStorage } from './adapters/hologram';

/**
 * Create a test budget with specified resources
 */
export function mkBudget(io: number = 1000, cpuMs: number = 100, mem: number = 64): Budget {
  return { io, cpuMs, mem };
}

/**
 * Create a test witness for given bytes
 */
export async function mkWitness(bytes: Buffer): Promise<Witness> {
  const verifier = await createVerifier();
  return {
    r96: verifier.r96(bytes),
    probes: 192, // Standard Klein probe count
    timestamp: Date.now(),
  };
}

/**
 * Create a test CTP instance
 */
export async function mkCTP(nodeId: string = 'test-node', lanes: number = 8, windowMs: number = 100) {
  return await createCTP({ nodeId, lanes, windowMs });
}

/**
 * Create a test storage instance
 */
export async function mkStorage() {
  return await createStorage({
    rows: 48,
    cols: 256,
    tileCols: 16,
    ec: { k: 3, m: 2 }, // 3 data + 2 parity
  });
}

/**
 * Assert that a receipt indicates successful operation and closed window
 */
export function assertReceiptClosed(receipt: Receipt, operation: string): void {
  if (!receipt.ok) {
    throw new Error(`Operation ${operation} failed: ${JSON.stringify(receipt.details)}`);
  }
  
  if (!receipt.windowClosed) {
    throw new Error(`Window not closed for ${operation}: ${JSON.stringify(receipt.details)}`);
  }
  
  console.log(`✅ ${operation} completed - window closed`);
}

/**
 * Assert that a budget is zero (fully consumed)
 */
export function assertBudgetZero(budget: Budget): void {
  if (budget.io !== 0 || budget.cpuMs !== 0 || (budget.mem || 0) !== 0) {
    throw new Error(`Budget not zero: ${JSON.stringify(budget)}`);
  }
}

/**
 * Assert that placement coordinates are within valid ranges
 */
export function assertValidPlacement(placements: Placement[]): void {
  if (placements.length < 3) {
    throw new Error(`Insufficient placements: ${placements.length} < 3`);
  }
  
  for (const p of placements) {
    if (p.r < 0 || p.r >= 48) {
      throw new Error(`Invalid row: ${p.r} (must be 0-47)`);
    }
    if (p.c < 0 || p.c >= 256) {
      throw new Error(`Invalid column: ${p.c} (must be 0-255)`);
    }
  }
  
  // Check that we have at least 2 distinct rows
  const rows = new Set(placements.map(p => p.r));
  if (rows.size < 2) {
    throw new Error(`Insufficient row diversity: ${rows.size} < 2`);
  }
}

/**
 * Assert that witness verification passes
 */
export async function assertWitnessValid(bytes: Buffer, witness: Witness): Promise<void> {
  const verifier = await createVerifier();
  const expectedR96 = verifier.r96(bytes);
  
  if (witness.r96 !== expectedR96) {
    throw new Error(`Witness verification failed: expected ${expectedR96}, got ${witness.r96}`);
  }
  
  console.log(`✅ Witness verified - r96: ${witness.r96.substring(0, 8)}...`);
}

/**
 * Create a test postcard message
 */
export function mkPostcard(message: string, from: string = 'Alice', to: string = 'Bob'): {
  message: string;
  from: string;
  to: string;
  timestamp: number;
  bytes: Buffer;
} {
  const data = {
    message,
    from,
    to,
    timestamp: Date.now(),
  };
  
  return {
    ...data,
    bytes: Buffer.from(JSON.stringify(data), 'utf8'),
  };
}

/**
 * Log placement information in a readable format
 */
export function logPlacement(id: string, placements: Placement[]): void {
  console.log(`📍 Placement for ${id.substring(0, 8)}...:`);
  placements.forEach((p, i) => {
    console.log(`   ${i + 1}. Row ${p.r}, Column ${p.c}`);
  });
}

/**
 * Log budget information
 */
export function logBudget(budget: Budget, operation: string): void {
  console.log(`💰 Budget for ${operation}: IO=${budget.io}, CPU=${budget.cpuMs}ms, Mem=${budget.mem || 0}MB`);
}

/**
 * Log receipt information
 */
export function logReceipt(receipt: Receipt, operation: string): void {
  console.log(`📋 Receipt for ${operation}:`);
  console.log(`   Status: ${receipt.ok ? '✅ OK' : '❌ FAILED'}`);
  console.log(`   Window: ${receipt.windowClosed ? '✅ CLOSED' : '⏳ OPEN'}`);
  console.log(`   Budget After: IO=${receipt.budgetAfter.io}, CPU=${receipt.budgetAfter.cpuMs}ms`);
  if (receipt.details.windowId) {
    console.log(`   Window ID: ${receipt.details.windowId}`);
  }
}

/**
 * Create a performance timer
 */
export class PerfTimer {
  private start: number;
  private name: string;
  
  constructor(name: string) {
    this.name = name;
    this.start = Date.now();
  }
  
  end(): number {
    const elapsed = Date.now() - this.start;
    console.log(`⏱️  ${this.name}: ${elapsed}ms`);
    return elapsed;
  }
}

/**
 * Run a performance test with multiple iterations
 */
export async function runPerfTest<T>(
  name: string,
  iterations: number,
  testFn: () => Promise<T>
): Promise<{ results: T[]; avgTime: number; totalTime: number }> {
  console.log(`🚀 Running performance test: ${name} (${iterations} iterations)`);
  
  const results: T[] = [];
  const start = Date.now();
  
  for (let i = 0; i < iterations; i++) {
    const result = await testFn();
    results.push(result);
  }
  
  const totalTime = Date.now() - start;
  const avgTime = totalTime / iterations;
  
  console.log(`📊 ${name} Results:`);
  console.log(`   Total time: ${totalTime}ms`);
  console.log(`   Average time: ${avgTime.toFixed(2)}ms`);
  console.log(`   Throughput: ${(1000 / avgTime).toFixed(2)} ops/sec`);
  
  return { results, avgTime, totalTime };
}

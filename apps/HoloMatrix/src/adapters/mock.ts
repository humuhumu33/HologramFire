/**
 * Mock Hologram Adapter Implementation
 * Provides deterministic mock behavior for development and testing
 */

import { createHash } from 'crypto';
import type {
  HologramAdapter,
  Verifier,
  CTP,
  Storage,
  Kernel,
  Budget,
  Witness,
  Receipt,
  LatticeCoord,
  ComputeKernel
} from '../types';

export class MockHologramAdapter implements HologramAdapter {
  private speedFactor: number;

  constructor() {
    this.speedFactor = parseInt(process.env.MOCK_SPEED_FACTOR || '1', 10);
  }

  async createVerifier(): Promise<Verifier> {
    return new MockVerifier();
  }

  async createCTP(opts: { nodeId: string; lanes: number; windowMs: number }): Promise<CTP> {
    return new MockCTP(opts, this.speedFactor);
  }

  async createStorage(opts: { rows: 48; cols: 256; tileCols: number; ec: { k: number; m: number } }): Promise<Storage> {
    return new MockStorage(opts);
  }

  async spawnKernel(opts: ComputeKernel): Promise<Kernel> {
    return new MockKernel(opts, this.speedFactor);
  }

  uorIdFromBytes(bytes: Buffer): string {
    const hash = createHash('sha256').update(bytes).digest('hex');
    return `uor:${hash.substring(0, 24)}`;
  }

  place(id: string, opts: { rows: 48; cols: 256; parity?: number }): LatticeCoord[] {
    const hash = createHash('sha256').update(id).digest();
    const coords: LatticeCoord[] = [];
    
    // Generate at least 3 coordinates across distinct rows
    const usedRows = new Set<number>();
    for (let i = 0; i < Math.max(3, (opts.parity || 0) + 1); i++) {
      let row: number;
      do {
        row = hash[i] % opts.rows;
      } while (usedRows.has(row) && usedRows.size < opts.rows);
      
      usedRows.add(row);
      const col = hash[i + 1] % opts.cols;
      coords.push({ r: row, c: col });
    }
    
    return coords;
  }

  capabilities(): { simd?: boolean; zeroCopy?: boolean } {
    return { simd: true, zeroCopy: false };
  }
}

class MockVerifier implements Verifier {
  r96(buf: Buffer): string {
    const hash = createHash('sha256').update(buf).digest('hex');
    return hash.substring(0, 24);
  }

  klein(frame: Buffer): boolean {
    // Mock always returns true for Klein verification
    return true;
  }

  budget = {
    add(a: Budget, b: Budget): Budget {
      return {
        cpuMs: a.cpuMs + b.cpuMs,
        io: a.io + b.io,
        mem: a.mem + b.mem
      };
    },

    sub(a: Budget, b: Budget): Budget {
      return {
        cpuMs: Math.max(0, a.cpuMs - b.cpuMs),
        io: Math.max(0, a.io - b.io),
        mem: Math.max(0, a.mem - b.mem)
      };
    },

    zero(): Budget {
      return { cpuMs: 0, io: 0, mem: 0 };
    },

    isZero(b: Budget): boolean {
      return b.cpuMs === 0 && b.io === 0 && b.mem === 0;
    }
  };
}

class MockCTP implements CTP {
  private nodeId: string;
  private lanes: number;
  private windowMs: number;
  private speedFactor: number;
  private windows: Map<string, { frames: number; bytes: number; startTime: number }> = new Map();
  private laneCounters: number[] = [];

  constructor(opts: { nodeId: string; lanes: number; windowMs: number }, speedFactor: number) {
    this.nodeId = opts.nodeId;
    this.lanes = opts.lanes;
    this.windowMs = opts.windowMs;
    this.speedFactor = speedFactor;
    this.laneCounters = new Array(opts.lanes).fill(0);
  }

  async handshake(info: unknown): Promise<boolean> {
    console.log(`G6.ctp.handshake ✅ peer=${this.nodeId}`);
    return true;
  }

  async send(args: {
    lane: number;
    payload: Buffer;
    budget: Budget;
    attach: { r96: string; probes: number };
  }): Promise<{ attach: unknown; lane: number }> {
    const { lane, payload, budget } = args;
    
    // Check budget
    if (budget.io <= 0) {
      throw new Error('Insufficient budget for send');
    }

    this.laneCounters[lane]++;
    const windowId = `W${Math.floor(Date.now() / this.windowMs)}`;
    
    // Track window statistics
    if (!this.windows.has(windowId)) {
      this.windows.set(windowId, { frames: 0, bytes: 0, startTime: Date.now() });
    }
    const window = this.windows.get(windowId)!;
    window.frames++;
    window.bytes += payload.length;

    console.log(`lane=${lane} frame=${payload.length}B G2.klein✅ r96✅ G1/G3 admit✅`);
    
    return { attach: { windowId, timestamp: Date.now() }, lane };
  }

  async recv(): Promise<{
    lane: number;
    payload: Buffer;
    frame: Buffer;
    windowId: string;
    header?: { r96: string };
  }> {
    // Mock receive - simulate receiving data
    const lane = Math.floor(Math.random() * this.lanes);
    const payload = Buffer.alloc(4096, 0x42); // Mock payload
    const windowId = `W${Math.floor(Date.now() / this.windowMs)}`;
    
    return {
      lane,
      payload,
      frame: payload,
      windowId,
      header: { r96: 'mock-r96-hash' }
    };
  }

  async settle(windowId: string): Promise<Receipt> {
    const window = this.windows.get(windowId);
    if (!window) {
      throw new Error(`Window ${windowId} not found`);
    }

    const duration = Date.now() - window.startTime;
    console.log(`window=${windowId} G6.settle → G4.receipt: closed (frames=${window.frames} bytes=${window.bytes})`);

    return {
      id: `receipt-${windowId}`,
      closed: true,
      timestamp: Date.now(),
      gate: 'G4.receipt',
      metadata: { frames: window.frames, bytes: window.bytes, duration }
    };
  }

  async close(): Promise<void> {
    this.windows.clear();
    this.laneCounters.fill(0);
  }
}

class MockStorage implements Storage {
  private data: Map<string, { bytes: Buffer; witness: Witness }> = new Map();
  private opts: { rows: 48; cols: 256; tileCols: number; ec: { k: number; m: number } };

  constructor(opts: { rows: 48; cols: 256; tileCols: number; ec: { k: number; m: number } }) {
    this.opts = opts;
  }

  async put(args: {
    id: string;
    bytes: Buffer;
    policy: unknown;
    budget: Budget;
    witness: Witness;
  }): Promise<Receipt> {
    const { id, bytes, budget, witness } = args;
    
    // Check budget
    if (budget.mem <= 0) {
      throw new Error('Insufficient memory budget for PUT');
    }

    this.data.set(id, { bytes, witness });
    
    console.log(`PUT id=${id} place→ [mock-coords] G1/G3 admit✅ G8.write✅ → G4.receipt: closed`);
    
    return {
      id: `put-${id}`,
      closed: true,
      timestamp: Date.now(),
      gate: 'G4.receipt',
      metadata: { size: bytes.length, witness: witness.r96 }
    };
  }

  async get(args: { id: string; policy?: unknown }): Promise<{ bytes: Buffer; witness: Witness }> {
    const { id } = args;
    const entry = this.data.get(id);
    
    if (!entry) {
      throw new Error(`Data not found for id: ${id}`);
    }

    console.log(`GET id=${id} G7.local.verify r96✅`);
    
    return entry;
  }

  async repair(args: { id: string; budget: Budget }): Promise<Receipt> {
    const { id, budget } = args;
    
    // Check budget
    if (budget.cpuMs <= 0) {
      throw new Error('Insufficient CPU budget for repair');
    }

    console.log(`REPAIR id=${id} G8.reconstruct✅ → G4.receipt: closed`);
    
    return {
      id: `repair-${id}`,
      closed: true,
      timestamp: Date.now(),
      gate: 'G4.receipt',
      metadata: { repaired: true }
    };
  }

  debug = {
    damage: async (args: { id: string; parts: number }): Promise<boolean> => {
      const { id, parts } = args;
      console.log(`DEBUG: Simulating damage to ${id} (${parts} parts)`);
      return true;
    }
  };
}

class MockKernel implements Kernel {
  private opts: ComputeKernel;
  private speedFactor: number;

  constructor(opts: ComputeKernel, speedFactor: number) {
    this.opts = opts;
    this.speedFactor = speedFactor;
  }

  async await(): Promise<{
    ok: boolean;
    outputs: Array<{ id: string; witness: Witness }>;
    receipts: { compute: Receipt; aggregate: Receipt };
  }> {
    const { inputs, budget } = this.opts;
    
    // Check budget
    if (budget.cpuMs <= 0) {
      throw new Error('Insufficient CPU budget for compute');
    }

    // Simulate compute time (scaled by speed factor)
    const computeTime = Math.max(1, Math.floor(budget.cpuMs / this.speedFactor));
    await new Promise(resolve => setTimeout(resolve, computeTime));

    // Generate mock outputs
    const outputs = inputs.map((input, i) => ({
      id: `output-${i}`,
      witness: {
        r96: `mock-output-r96-${i}`,
        timestamp: Date.now(),
        nodeId: 'mock-node'
      }
    }));

    const computeReceipt: Receipt = {
      id: `compute-${Date.now()}`,
      closed: true,
      timestamp: Date.now(),
      gate: 'G4.receipt',
      metadata: { budgetAfter: { cpuMs: 0, io: 0, mem: 0 } }
    };

    const aggregateReceipt: Receipt = {
      id: `aggregate-${Date.now()}`,
      closed: true,
      timestamp: Date.now(),
      gate: 'G4.receipt',
      metadata: { windowClosure: 1.0 }
    };

    console.log(`compute receipt G4: closed; budgetAfter={cpuMs:0, io:0, mem:0}`);
    console.log(`aggregate window W42: closed=100%`);

    return {
      ok: true,
      outputs,
      receipts: { compute: computeReceipt, aggregate: aggregateReceipt }
    };
  }
}

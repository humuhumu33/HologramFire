/**
 * Core types for Hologram Virtual Infrastructure Demo
 * 
 * These types define the interface between the demo and the Hologram SDK,
 * whether using the mock implementation or the real SDK.
 */

export interface Budget {
  io: number;
  cpuMs: number;
  mem?: number;
}

export interface Witness {
  r96: string;        // 24-hex checksum for verification
  probes: number;     // Number of Klein probes used
  timestamp: number;  // When witness was created
}

export interface Receipt {
  ok: boolean;
  windowClosed: boolean;
  budgetAfter: Budget;
  details: {
    operation: string;
    timestamp: number;
    windowId?: string;
    [key: string]: any;
  };
}

export interface Placement {
  r: number;  // Row (0-47)
  c: number;  // Column (0-255)
}

export interface Verifier {
  r96: (bytes: Buffer) => string;
  klein: (frame: Buffer) => boolean;
  budget: {
    add: (a: Budget, b: Budget) => Budget;
    sub: (a: Budget, b: Budget) => Budget;
    zero: () => Budget;
    isZero: (b: Budget) => boolean;
  };
}

export interface CTP {
  handshake: (info: any) => Promise<boolean>;
  send: (args: {
    lane: number;
    payload: Buffer;
    budget: Budget;
    attach: { r96: string; probes: number };
  }) => Promise<{ attach: any; lane: number }>;
  recv: () => Promise<{
    lane: number;
    payload: Buffer;
    frame: Buffer;
    windowId: string;
  }>;
  settle: (windowId: string) => Promise<Receipt>;
  close: () => Promise<void>;
}

export interface Storage {
  put: (args: {
    id: string;
    bytes: Buffer;
    policy: any;
    budget: Budget;
    witness: Witness;
  }) => Promise<Receipt>;
  get: (args: {
    id: string;
    policy?: any;
  }) => Promise<{ bytes: Buffer; witness: Witness }>;
  repair: (args: { id: string; budget: Budget }) => Promise<Receipt>;
  debug?: {
    damage: (args: { id: string; parts: number }) => Promise<boolean>;
  };
}

export interface Kernel {
  await: () => Promise<{
    ok: boolean;
    outputs: Array<{ id: string; witness: Witness }>;
    receipts: {
      compute: Receipt;
      aggregate: Receipt;
    };
  }>;
}

export interface Postcard {
  id: string;
  message: string;
  from: string;
  to: string;
  timestamp: number;
  bytes: Buffer;
}

export interface LatticeConfig {
  rows: number;
  cols: number;
  tileCols: number;
  ec: {
    k: number;
    m: number;
  };
}

export interface CTPConfig {
  nodeId: string;
  lanes: number;
  windowMs: number;
}

export interface KernelConfig {
  name: string;
  inputs: Array<{ id: string }>;
  budget: Budget;
  pin?: {
    near?: string;
    lane?: number;
  };
  iopolicy?: {
    lane?: number;
    windowMs?: number;
  };
}

/**
 * Core types for Hologram Virtual Infra MatMul Demo
 * 12,288 lattice (48×256) with verifiable streaming matrix multiplication
 */

export type Budget = { io: number; cpuMs: number; mem?: number };

export type Witness = { 
  r96: string; 
  timestamp?: number; 
  nodeId?: string; 
};

export type Receipt = {
  id?: string;
  ok: boolean;
  closed?: boolean;
  windowClosed: boolean;
  budgetAfter: Budget;
  gate?: string;
  details?: Record<string, unknown>;
};

export type MatrixBlock = {
  id: string;            // UOR-ID for the block
  i: number;             // block row index
  j: number;             // block col index
  bytes: Buffer;         // serialized block data
};

export type StageLatency = {
  p50: number; p90: number; p99: number;
};

export type RunStats = {
  gbps: number; fps: number;
  sent: number; delivered: number; rejected: number;
  settleClosed: number; settleTotal: number;
  transport: StageLatency; storage: StageLatency; compute: StageLatency; e2e: StageLatency;
  cpuPercent: number;
  laneUtil: Array<{ lane: number; frames: number }>;
};

export interface Metrics {
  throughputGbps: number;
  transport: {
    p50Ms: number;
    p99Ms: number;
    framesSent: number;
    framesReceived: number;
    windowsTotal: number;
    windowsClosed: number;
    rejects: number;
  };
  storage: {
    p50Ms: number;
    p99Ms: number;
    puts: number;
    gets: number;
    repairs: number;
  };
  compute: {
    p50Ms: number;
    p99Ms: number;
    kernels: number;
    receipts: number;
  };
  e2e: {
    p50Ms: number;
    p99Ms: number;
  };
}

export interface LatticeCoord {
  r: number; // row (0-47)
  c: number; // column (0-255)
}

export interface PlacementPolicy {
  replicas: number;
  parity: number;
  faultDomains: number;
}

export interface TransportFrame {
  lane: number;
  payload: Buffer;
  windowId: string;
  r96: string;
  timestamp: number;
}

export interface ComputeKernel {
  name: string;
  inputs: Array<{ id: string }>;
  outputs: Array<{ id: string; witness: Witness }>;
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

export interface MatMulConfig {
  size: number;        // matrix side (default 2048)
  block: number;       // block size (default 128)
  lanes: number;       // transport lanes (default 64)
  payload: number;     // frame size in bytes (default 4096)
  batch: number;       // frames per batch (default 16)
  workers: number;     // worker threads (default 4-8)
  window: number;      // settlement window in ms (default 100)
  targetGbps: number;  // target throughput (default 25.0)
}

export interface BenchConfig {
  duration: number;    // test duration in seconds
  lanes: number;
  payload: number;
  batch: number;
  workers: number;
  window: number;
  target: number;      // target Gbps
}

export interface LoadGenResult {
  throughputGbps: number;
  latency: {
    p50: number;
    p99: number;
  };
  framesSent: number;
  framesReceived: number;
  windowsTotal: number;
  windowsClosed: number;
  rejects: number;
  laneUtilization: number[];
  duration: number;
}

export interface HistogramBucket {
  min: number;
  max: number;
  count: number;
}

export interface Histogram {
  buckets: HistogramBucket[];
  total: number;
  p50: number;
  p90: number;
  p99: number;
}

export interface GateResult {
  gate: string;
  success: boolean;
  timestamp: number;
  metadata?: Record<string, unknown>;
}

export interface Verifier {
  r96(buf: Buffer): string;
  klein(frame: Buffer): boolean;
  budget: {
    add(a: Budget, b: Budget): Budget;
    sub(a: Budget, b: Budget): Budget;
    zero(): Budget;
    isZero(b: Budget): boolean;
  };
}

export interface CTP {
  handshake(info: unknown): Promise<boolean>;
  send(args: {
    lane: number;
    payload: Buffer;
    budget: Budget;
    attach: { r96: string; probes: number };
  }): Promise<{ attach: unknown; lane: number }>;
  recv(): Promise<{
    lane: number;
    payload: Buffer;
    frame: Buffer;
    windowId: string;
    header?: { r96: string };
  }>;
  settle(windowId: string): Promise<Receipt>;
  close(): Promise<void>;
}

export interface Storage {
  put(args: {
    id: string;
    bytes: Buffer;
    policy: unknown;
    budget: Budget;
    witness: Witness;
  }): Promise<Receipt>;
  get(args: { id: string; policy?: unknown }): Promise<{ bytes: Buffer; witness: Witness }>;
  repair(args: { id: string; budget: Budget }): Promise<Receipt>;
  debug?: {
    damage(args: { id: string; parts: number }): Promise<boolean>;
  };
}

export interface Kernel {
  await(): Promise<{
    ok: boolean;
    outputs: Array<{ id: string; witness: Witness }>;
    receipts: { compute: Receipt; aggregate: Receipt };
  }>;
}

export interface HologramAdapter {
  createVerifier(): Promise<Verifier>;
  createCTP(opts: {
    nodeId: string;
    lanes: number;
    windowMs: number;
  }): Promise<CTP>;
  createStorage(opts: {
    rows: 48;
    cols: 256;
    tileCols: number;
    ec: { k: number; m: number };
  }): Promise<Storage>;
  spawnKernel(opts: ComputeKernel): Promise<Kernel>;
  uorIdFromBytes(bytes: Buffer): string;
  place(id: string, opts: { rows: 48; cols: 256; parity?: number }): LatticeCoord[];
  capabilities?(): { simd?: boolean; zeroCopy?: boolean };
}

// Gate constants for logging
export const GATES = {
  HOLOGRAM_ORACLE: 'G0.hologram-oracle',
  STRICT_HOLOGRAPHIC_COHERENCE: 'G0.strict-holographic-coherence-oracle',
  HOLOGRAPHY: 'G1.holography',
  CONSERVATION: 'G1.conservation',
  RESONANCE: 'G1.resonance',
  KLEIN: 'G2.klein',
  R96_SEMIRING: 'G3.r96.semiring',
  RECEIPT: 'G4.receipt',
  BOUNDARY: 'G4.boundary',
  UORID_KAT: 'G5.uorid.kat',
  FIXTURES: 'G5.fixtures',
  CTP_HANDSHAKE: 'G6.ctp.handshake',
  CTP_WINDOW: 'G6.ctp.window',
  CTP_FAIL: 'G6.ctp.fail',
  VPI_REGISTRY: 'G7.vpi.registry',
  LOCAL_VERIFIER: 'G7.local.verifier',
  OBJECT: 'G8.object'
} as const;

export type GateName = typeof GATES[keyof typeof GATES];

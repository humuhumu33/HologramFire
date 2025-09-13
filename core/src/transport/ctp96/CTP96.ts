import crypto from "node:crypto";
import { stableStringify } from "../../crypto/util/stable";
import { ccmHash } from "../../crypto/ccm/CCMHash";
import { classifyR96 } from "../../core/resonance/R96";
import { proofFromBudgets } from "../../logic/proof/Proof";
import { buildReceipt, verifyReceipt, BudgetReceipt } from "../../crypto/receipt/BudgetReceipt";

export type NonceHex = string;
export type Seq = number;

export type Kind = "OFFER" | "COUNTER" | "ACCEPT" | "DATA";

export interface HandshakeMeta {
  module: string;              // module initiating the session
  algo: "ctp96";
  note?: string;
}

export interface BaseFrame {
  kind: Kind;
  ts: string;                  // ISO time
  nonce: NonceHex;             // replay protection
  seq: Seq;                    // strict ordering
  meta?: HandshakeMeta;        // present in handshake frames
  // integrity
  hash: string;                // CCM hash of payload (domain "ctp96")
  r96: number;                 // resonance checksum of payload
}

export interface HandshakeFrame extends BaseFrame {
  kind: "OFFER" | "COUNTER" | "ACCEPT";
  budgets: number[];           // proof budgets for witness-on-wire
  receipt: BudgetReceipt;      // witness + ok flag
}

export interface DataFrame extends BaseFrame {
  kind: "DATA";
  data: unknown;
}

export type Frame = HandshakeFrame | DataFrame;

export function randomNonce(bytes = 12): NonceHex {
  return crypto.randomBytes(bytes).toString("hex");
}

function payloadForHash(f: Omit<Frame, "hash" | "r96">): string {
  // stable, annotation-free, without integrity fields
  return stableStringify(f);
}

function computeIntegrity(f: Omit<Frame, "hash" | "r96">) {
  const payload = payloadForHash(f);
  const hash = ccmHash(payload, "ctp96");
  const r96 = classifyR96(Array.from(Buffer.from(payload, "utf8").values()));
  return { hash, r96 };
}

export function makeOffer(moduleId: string, budgets: number[], note?: string): HandshakeFrame {
  const base: Omit<HandshakeFrame, "hash" | "r96" | "receipt"> = {
    kind: "OFFER",
    ts: new Date().toISOString(),
    nonce: randomNonce(),
    seq: 0,
    meta: { module: moduleId, algo: "ctp96", note },
    budgets,
  } as any;
  const receipt = buildReceipt(proofFromBudgets(budgets));
  const { hash, r96 } = computeIntegrity({ ...base, receipt } as any);
  return { ...(base as any), receipt, hash, r96 };
}

export function makeCounter(offer: HandshakeFrame, budgets: number[], note?: string): HandshakeFrame {
  const base: Omit<HandshakeFrame, "hash" | "r96" | "receipt"> = {
    kind: "COUNTER",
    ts: new Date().toISOString(),
    nonce: randomNonce(),
    seq: 1,
    meta: { module: offer.meta?.module ?? "unknown", algo: "ctp96", note },
    budgets,
  } as any;
  const receipt = buildReceipt(proofFromBudgets(budgets));
  const { hash, r96 } = computeIntegrity({ ...base, receipt } as any);
  return { ...(base as any), receipt, hash, r96 };
}

export function makeAccept(counter: HandshakeFrame, budgets: number[], note?: string): HandshakeFrame {
  const base: Omit<HandshakeFrame, "hash" | "r96" | "receipt"> = {
    kind: "ACCEPT",
    ts: new Date().toISOString(),
    nonce: randomNonce(),
    seq: 2,
    meta: { module: counter.meta?.module ?? "unknown", algo: "ctp96", note },
    budgets,
  } as any;
  const receipt = buildReceipt(proofFromBudgets(budgets));
  const { hash, r96 } = computeIntegrity({ ...base, receipt } as any);
  return { ...(base as any), receipt, hash, r96 };
}

export function makeData(seq: number, data: unknown): DataFrame {
  const base: Omit<DataFrame, "hash" | "r96"> = {
    kind: "DATA",
    ts: new Date().toISOString(),
    nonce: randomNonce(),
    seq,
    data,
  } as any;
  const { hash, r96 } = computeIntegrity(base as any);
  return { ...(base as any), hash, r96 };
}

export class SessionVerifier {
  private seenNonces = new Set<string>();
  private phase: 0 | 1 | 2 | 3 = 0; // 0=expect OFFER, 1=COUNTER, 2=ACCEPT, 3=DATA
  private lastSeq: number = -1;

  verify(frame: Frame): boolean {
    // Replay
    if (this.seenNonces.has(frame.nonce)) throw new Error("replay_detected");
    this.seenNonces.add(frame.nonce);

    // Integrity (hash + r96)
    const { hash, r96 } = computeIntegrity(stripIntegrity(frame));
    if (hash !== frame.hash) throw new Error("hash_mismatch");
    if (r96 !== frame.r96) throw new Error("r96_mismatch");

    // Phase + sequencing
    switch (frame.kind) {
      case "OFFER":
        if (this.phase !== 0 || frame.seq !== 0) throw new Error("handshake_order_error");
        this.assertWitness(frame);
        this.phase = 1;
        this.lastSeq = frame.seq;
        return true;
      case "COUNTER":
        if (this.phase !== 1 || frame.seq !== 1) throw new Error("handshake_order_error");
        this.assertWitness(frame);
        this.phase = 2;
        this.lastSeq = frame.seq;
        return true;
      case "ACCEPT":
        if (this.phase !== 2 || frame.seq !== 2) throw new Error("handshake_order_error");
        this.assertWitness(frame);
        this.phase = 3;
        this.lastSeq = frame.seq;
        return true;
      case "DATA":
        if (this.phase !== 3) throw new Error("data_before_accept");
        if (frame.seq !== this.lastSeq + 1) throw new Error("out_of_order");
        this.lastSeq = frame.seq;
        return true;
    }
  }

  private assertWitness(f: HandshakeFrame) {
    if (!Array.isArray(f.budgets) || !f.receipt) throw new Error("missing_witness");
    if (!verifyReceipt(proofFromBudgets(f.budgets), f.receipt)) throw new Error("invalid_witness");
    if (f.receipt.ok !== true) throw new Error("witness_not_ok");
  }
}

function stripIntegrity<T extends Frame>(f: T): Omit<T, "hash" | "r96"> {
  const { hash, r96, ...rest } = f as any;
  return rest;
}

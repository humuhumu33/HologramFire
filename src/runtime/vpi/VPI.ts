import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface VerifyCost { cycles: number; pages: number; }
export interface VerifyOptions { budget?: number[]; context?: Record<string, unknown>; }
export interface VerifyResult { ok: boolean; reason?: string; witness?: string; cost: VerifyCost; }

export interface Verifier {
  id: string;
  version: string;
  verify(input: unknown, opts?: VerifyOptions): Promise<VerifyResult>;
}

export class VpiRegistry {
  private map = new Map<string, Verifier>();
  register(moduleId: string, v: Verifier) {
    if (this.map.has(moduleId)) throw new Error("verifier_already_registered");
    this.map.set(moduleId, v);
  }
  get(moduleId: string): Verifier {
    const v = this.map.get(moduleId);
    if (!v) throw new Error("verifier_not_found");
    return v;
  }
  size() { return this.map.size; }
}

/** Minimal cost model: cycles ~ payload bytes, pages ~ ceil(bytes/4096) */
export function estimateCost(payload: unknown): VerifyCost {
  const s = JSON.stringify(payload ?? "");
  const bytes = Buffer.byteLength(s, "utf8");
  return { cycles: bytes, pages: Math.max(1, Math.ceil(bytes / 4096)) };
}

export function makeWitness(domain: string, payload: unknown): string {
  return ccmHash(payload, domain);
}

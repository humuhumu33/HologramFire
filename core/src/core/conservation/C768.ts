import { N } from "../constants";

export const C768_SIZE = 768;

/**
 * Deterministic round-robin schedule over 768 slots.
 * Property: each slot appears exactly once; rotation by `seed`.
 */
export function generateC768Schedule(seed = 0): number[] {
  const s = ((seed % C768_SIZE) + C768_SIZE) % C768_SIZE;
  const out = new Array<number>(C768_SIZE);
  for (let i = 0; i < C768_SIZE; i++) out[i] = (i + s) % C768_SIZE;
  return out;
}

export function verifyC768Schedule(seq: number[]): { ok: boolean; reason?: string } {
  if (!Array.isArray(seq)) return { ok: false, reason: "not an array" };
  if (seq.length !== C768_SIZE) return { ok: false, reason: "wrong length" };
  const seen = new Set<number>();
  let sum = 0;
  for (const x of seq) {
    if (!Number.isInteger(x) || x < 0 || x >= C768_SIZE) return { ok: false, reason: "out of range" };
    if (seen.has(x)) return { ok: false, reason: "duplicate" };
    seen.add(x);
    sum += x;
  }
  const expectSum = (C768_SIZE * (C768_SIZE - 1)) / 2; // 0..767
  if (sum !== expectSum) return { ok: false, reason: "bad sum" };
  return { ok: true };
}

/**
 * Optional fairness check: for the canonical generator, successive diffs are 1 mod 768.
 */
export function verifyRotationFairness(seq: number[]): boolean {
  if (seq.length !== C768_SIZE) return false;
  for (let i = 0; i < C768_SIZE; i++) {
    const a = seq[i];
    const b = seq[(i + 1) % C768_SIZE];
    if (((a + 1) % C768_SIZE) !== b) return false;
  }
  return true;
}

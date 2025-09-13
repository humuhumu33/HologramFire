import { R_CLASSES } from "../constants";

function assertByte(n: number): void {
  if (!Number.isFinite(n)) throw new Error("Non-finite value in vector");
}

/**
 * Minimal R96 classifier stub: maps any numeric vector → class in [0,95].
 * Implementation: sum elements modulo 96. Deterministic, total, fast.
 */
export function classifyR96(vec: number[]): number {
  if (!Array.isArray(vec)) throw new Error("classifyR96: vec must be an array");
  let acc = 0;
  for (const v of vec) {
    assertByte(v);
    acc = (acc + (v | 0)) % R_CLASSES;
  }
  return (acc + R_CLASSES) % R_CLASSES;
}

/** Convenience helper to classify single value quickly */
export function classifyR96Scalar(v: number): number {
  assertByte(v);
  return ((v | 0) % R_CLASSES + R_CLASSES) % R_CLASSES;
}

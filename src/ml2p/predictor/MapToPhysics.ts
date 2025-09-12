import { witness } from "../Stable";

export type Arch = { paramsM: number; depth: number; width: number; device: any };
export function predict(arch: Arch) {
  // Simple, deterministic baseline: J ≈ c1*params + c2*depth + c3*width; fake A/P/R/F1 bounded
  const c1 = 3e-9, c2 = 1e-2, c3 = 5e-3;
  const predJ = c1*arch.paramsM*1e6 + c2*arch.depth + c3*arch.width;
  const predAPRf1 = { a: 0.70 + 0.02*Math.tanh(arch.depth/64), p: 0.72, r: 0.71, f1: 0.715 };
  return { predJ, predAPRf1, witness: witness("ml2p.predict", { arch, predJ }) };
}

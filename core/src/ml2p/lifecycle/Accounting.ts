import { witness } from "../Stable";

export type PhaseJ = { dataset: number; training: number; retraining: number; inference: number };
export function reconcile(phases: PhaseJ) {
  for (const k of Object.keys(phases)) {
    const v = (phases as any)[k];
    if (typeof v !== "number" || !isFinite(v) || v < 0) throw new Error("energy must be >=0");
  }
  const total = phases.dataset + phases.training + phases.retraining + phases.inference;
  return { totalJ: total, witness: witness("ml2p.lifecycle", { phases, total }) };
}

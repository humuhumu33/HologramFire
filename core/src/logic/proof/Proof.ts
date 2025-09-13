import { C96, sum, norm } from "../rl96/RL96";

export interface ProofStep { budget: C96; note?: string; }
export interface Proof { steps: ProofStep[]; }

export function verifyProof(p: Proof): boolean {
  return norm(sum(p.steps.map(s => s.budget))) === 0;
}
export function composeProofs(a: Proof, b: Proof): Proof {
  return { steps: [...a.steps, ...b.steps] };
}
export function proofFromBudgets(budgets: number[]): Proof {
  return { steps: budgets.map((b, i) => ({ budget: norm(b), note: `step-${i}` })) };
}

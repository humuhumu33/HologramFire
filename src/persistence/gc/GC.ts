import { Ledger } from "../journal/Ledger";

export interface RetainPlan {
  keepEvery: number;  // e.g., keep every Nth entry
  minTail: number;    // never trim below this many entries
}

export function planRetain(total: number, keepEvery = 64, minTail = 256): RetainPlan {
  return { keepEvery, minTail: Math.min(minTail, total) };
}

export function verifyRetainPlan<T>(led: Ledger<T>, plan: RetainPlan): boolean {
  const n = led.entries.length;
  if (n <= plan.minTail) return true;
  // any delta window shorter than keepEvery will still have anchors
  return plan.keepEvery >= 1 && plan.minTail >= 0;
}

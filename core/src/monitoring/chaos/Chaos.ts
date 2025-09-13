import { Metrics } from "../metrics/Metrics";
import { evaluateRules, AlertRule, Alert } from "../alerts/Rules";

/** xorshift32 deterministic RNG */
function* xorshift32(seed = 0xC0FFEE) {
  let x = seed >>> 0;
  while (true) {
    x ^= x << 13; x >>>= 0;
    x ^= x >>> 17; x >>>= 0;
    x ^= x << 5;  x >>>= 0;
    yield x >>> 0;
  }
}

export interface ChaosPlan {
  iterations: number;
  violationRate: number; // 0..1
  seed?: number;
}

/** Runs a deterministic chaos loop that records violations at a configured rate. */
export function runChaos(m: Metrics, rules: AlertRule[], plan: ChaosPlan): { alerts: Alert[] } {
  const rng = xorshift32(plan.seed ?? 0xDEADBEEF);
  for (let i = 0; i < plan.iterations; i++) {
    const r = (rng.next().value as number) / 0xffffffff;
    if (r < plan.violationRate) {
      m.recordViolation("holographic_correspondence", { iter: i, seed: plan.seed ?? 0xDEADBEEF });
    } else {
      m.inc("ok_ticks", 1);
    }
  }
  const alerts = evaluateRules(m, rules);
  return { alerts };
}

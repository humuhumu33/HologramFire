import { Metrics } from "../metrics/Metrics";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface AlertRule {
  id: string;
  violationsAtLeast?: number;
  counterAtLeast?: { name: string; value: number };
}

export interface Alert {
  id: string; reason: string; witness: string;
}

export function metricsWitness(m: Metrics): string {
  return m.witness();
}

export function evaluateRules(m: Metrics, rules: AlertRule[]): Alert[] {
  const snap = m.snapshot();
  const w = metricsWitness(m);
  const out: Alert[] = [];
  for (const r of rules) {
    let trig = false;
    let why = "";
    if (r.violationsAtLeast !== undefined && snap.violations >= r.violationsAtLeast) {
      trig = true; why = `violations>=${r.violationsAtLeast}`;
    }
    if (!trig && r.counterAtLeast) {
      const got = snap.counters[r.counterAtLeast.name] || 0;
      if (got >= r.counterAtLeast.value) { trig = true; why = `counter(${r.counterAtLeast.name})>=${r.counterAtLeast.value}`; }
    }
    if (trig) {
      out.push(buildAlert(r.id, why, w));
    }
  }
  return out;
}

export function buildAlert(id: string, reason: string, telemetryWitness: string): Alert {
  const witness = ccmHash({ id, reason, telemetryWitness }, "alert.rule");
  return { id, reason, witness };
}

export function verifyAlert(a: Alert, telemetryWitness: string): boolean {
  const expect = ccmHash({ id: a.id, reason: a.reason, telemetryWitness }, "alert.rule");
  return expect === a.witness;
}

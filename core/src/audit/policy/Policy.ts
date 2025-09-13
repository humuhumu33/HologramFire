import { SessionVerifier, Frame } from "../../transport/ctp96/CTP96";
import { Metrics } from "../../monitoring/metrics/Metrics";
import { evaluateRules, buildAlert } from "../../monitoring/alerts/Rules";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface RunOutcome {
  ok: boolean;
  reason?: string;
  alerts?: ReturnType<typeof evaluateRules>;
  witness: string;
}

/** Run an attack trace against the transport verifier; fail-closed on any violation. */
export function runAttack(name: string, frames: Frame[], m: Metrics): RunOutcome {
  const sv = new SessionVerifier();
  try {
    for (const f of frames) sv.verify(f);
    // If attacker frames pass, that's a policy violation.
    m.recordViolation("forgery_resistance", { name, passed: true });
    const w = ccmHash({ name, passed: true }, "attack.run");
    return { ok: false, reason: "attack_passed", alerts: [], witness: w };
  } catch (e: any) {
    // Fail-closed is expected; emit a positive alert witness
    const alert = buildAlert(`attack:${name}`, e?.message || "error", m.witness());
    const w = ccmHash({ name, reason: e?.message || "error", alert }, "attack.run");
    return { ok: true, alerts: [alert], witness: w };
  }
}

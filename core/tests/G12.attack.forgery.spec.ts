import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { forgeryAttack } from "../src/audit/attacks/Attacks";
import { runAttack } from "../src/audit/policy/Policy";

describe("G12: Forgery attack fails closed", () => {
  it("forged frames are rejected by verifier", () => {
    const m = new Metrics();
    const t = forgeryAttack();
    const out = runAttack(t.name, t.frames, m);
    expect(out.ok).toBe(true);
  });
});

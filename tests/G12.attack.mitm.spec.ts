import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { mitmAttack } from "../src/audit/attacks/Attacks";
import { runAttack } from "../src/audit/policy/Policy";

describe("G12: MITM attack fails closed", () => {
  it("tampered integrity is rejected", () => {
    const m = new Metrics();
    const t = mitmAttack();
    const out = runAttack(t.name, t.frames, m);
    expect(out.ok).toBe(true);
  });
});

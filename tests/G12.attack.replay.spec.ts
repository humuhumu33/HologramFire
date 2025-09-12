import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { replayAttack } from "../src/audit/attacks/Attacks";
import { runAttack } from "../src/audit/policy/Policy";

describe("G12: Replay attack fails closed", () => {
  it("duplicate nonce is detected", () => {
    const m = new Metrics();
    const t = replayAttack();
    const out = runAttack(t.name, t.frames, m);
    expect(out.ok).toBe(true);
    expect(typeof out.witness).toBe("string");
  });
});

import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { runChaos } from "../src/monitoring/chaos/Chaos";

describe("G11: Chaos produces violations and alerts deterministically", () => {
  const rules = [{ id: "R-viol", violationsAtLeast: 2 }];
  it("deterministic: seed+rate → alerts", () => {
    const m = new Metrics();
    const { alerts } = runChaos(m, rules as any, { iterations: 4, violationRate: 0.75, seed: 1234 });
    expect(m.snapshot().violations).toBeGreaterThanOrEqual(2);
    expect(alerts.length).toBe(1);
  });
});

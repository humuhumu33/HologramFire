import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { evaluateRules, metricsWitness, verifyAlert } from "../src/monitoring/alerts/Rules";

describe("G11: Alerts fire on violations with verifiable witnesses", () => {
  const rules = [{ id: "R1", violationsAtLeast: 1 }];
  it("triggers when violations >= threshold", () => {
    const m = new Metrics();
    m.recordViolation("holographic_correspondence");
    const alerts = evaluateRules(m, rules as any);
    expect(alerts.length).toBe(1);
    const tw = metricsWitness(m);
    expect(verifyAlert(alerts[0], tw)).toBe(true);
    // tamper witness -> fail-closed
    const bad = { ...alerts[0], witness: "deadbeef" };
    expect(verifyAlert(bad as any, tw)).toBe(false);
  });
});

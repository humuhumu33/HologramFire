import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";

describe("G11: Metrics telemetry & witness", () => {
  it("telemetry witness stable for same state and changes when state mutates", () => {
    const m = new Metrics();
    m.inc("events_total", 1);
    m.setGauge("queue_depth", 3);
    m.observe("verify_ms", 12);
    const w1 = m.witness();
    const w2 = m.witness();
    expect(w1).toBe(w2);     // stable
    m.inc("events_total", 1);
    const w3 = m.witness();
    expect(w3).not.toBe(w1); // changed state
  });
});

import { describe, it, expect } from "vitest";
import { predict } from "../src/ml2p/predictor/MapToPhysics";
describe("G-ML2P: predictor", () => {
  it("predicts positive J and plausible f1", () => {
    const r = predict({ paramsM: 20, depth: 16, width: 256, device:{cpu:"A"} });
    expect(r.predJ).toBeGreaterThan(0);
    expect(r.predAPRf1.f1).toBeGreaterThan(0.5);
    expect(r.witness.length).toBe(64);
  });
});

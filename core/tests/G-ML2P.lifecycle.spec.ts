import { describe, it, expect } from "vitest";
import { reconcile } from "../src/ml2p/lifecycle/Accounting";
describe("G-ML2P: lifecycle accounting", () => {
  it("sums phases to total with witness", () => {
    const r = reconcile({ dataset:0.2, training: 1.0, retraining: 0.3, inference: 0.1 });
    expect(r.totalJ).toBeCloseTo(1.6, 9);
    expect(r.witness.length).toBe(64);
  });
});

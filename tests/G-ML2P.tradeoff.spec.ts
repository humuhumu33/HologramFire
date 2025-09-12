import { describe, it, expect } from "vitest";
import { buildPareto } from "../src/ml2p/objective/Tradeoff";
describe("G-ML2P: Pareto tradeoff", () => {
  it("emits non-dominated set with witness", () => {
    const { pareto, witness } = buildPareto([{ j:1.0, f1:0.70 }, { j:0.8, f1:0.69 }, { j:1.2, f1:0.72 }]);
    expect(pareto.length).toBeGreaterThanOrEqual(2);
    expect(witness.length).toBe(64);
  });
});

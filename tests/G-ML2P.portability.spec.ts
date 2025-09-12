import { describe, it, expect } from "vitest";
import { normalize } from "../src/ml2p/hardware/Portability";
describe("G-ML2P: hardware portability", () => {
  it("normalizes j/op and binds calibration witness", () => {
    const out = normalize([{ device:{cpu:"A"}, j:1.0, ops:1e6 }, { device:{cpu:"B"}, j:0.8, ops:1e6 }], { device:{cpu:"A"}, factor:0.9 });
    expect(out.normalized[0].jPerOp).toBeCloseTo(0.9/1e6, 12);
    expect(out.witness.length).toBe(64);
  });
});

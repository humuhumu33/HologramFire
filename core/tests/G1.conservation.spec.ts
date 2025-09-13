import { describe, it, expect } from "vitest";
import { generateC768Schedule, verifyC768Schedule, verifyRotationFairness } from "../src/core/conservation/C768";

describe("G1: C768 schedule properties", () => {
  it("generates a valid permutation for several seeds", () => {
    for (const s of [0, 1, 7, 127, 768, -3]) {
      const seq = generateC768Schedule(s);
      const res = verifyC768Schedule(seq);
      expect(res.ok).toBe(true);
    }
  });

  it("default schedule has rotation fairness (diff=+1 mod 768)", () => {
    const seq = generateC768Schedule(0);
    expect(verifyRotationFairness(seq)).toBe(true);
  });
});

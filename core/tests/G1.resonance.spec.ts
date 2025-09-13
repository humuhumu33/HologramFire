import { describe, it, expect } from "vitest";
import { classifyR96, classifyR96Scalar } from "../src/core/resonance/R96";

describe("G1: R96 resonance classification", () => {
  it("covers exactly 96 classes for scalars 0..95", () => {
    const seen = new Set<number>();
    for (let k = 0; k < 96; k++) seen.add(classifyR96Scalar(k));
    expect(seen.size).toBe(96);
  });

  it("is deterministic for vectors", () => {
    const v = [1, 2, 3, 4, 5, 6];
    const a = classifyR96(v);
    const b = classifyR96(v);
    expect(a).toBe(b);
    expect(a).toBeGreaterThanOrEqual(0);
    expect(a).toBeLessThan(96);
  });
});

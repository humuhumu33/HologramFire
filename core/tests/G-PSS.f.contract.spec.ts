import { describe, it, expect } from "vitest";
import { makeHRF } from "../src/prime/HRF";
import { applyF } from "../src/prime/F";

describe("G-PSS: Endofunctor contract", () => {
  it("F is deterministic with stable witness", () => {
    const x = makeHRF(1);
    const a = applyF(x), b = applyF(x);
    expect(a.witness).toBeTypeOf("string");
    expect(a.witness.length).toBeGreaterThan(0);
    expect(a.out).toEqual(b.out);
  });
});

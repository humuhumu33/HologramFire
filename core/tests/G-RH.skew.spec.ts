import { describe, it, expect } from "vitest";
import { skew } from "../src/rh/Skew";

describe("G-RH: UN mirror-skew witness", () => {
  it("symmetric -> zero; asymmetric -> nonzero", () => {
    const sym = Array(96).fill(0); sym[24]=3; sym[25]=3;
    expect(Math.abs(skew(sym,24).delta)).toBe(0);
    
    const asym = Array(96).fill(0); asym[24]=3; asym[25]=1;
    expect(Math.abs(skew(asym,24).delta)).toBeGreaterThan(0);
  });
});

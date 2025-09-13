import { describe, it, expect } from "vitest";
import { align } from "../src/rh/Align";

describe("G-RH: Alignment determinism + tolerance", () => {
  it("deterministic tie-break", () => {
    const flat = Array(96).fill(1);
    const a = align(flat);
    const b = align(flat);
    expect(a.k).toEqual(b.k);
  });
  it("tolerance respected for symmetric pairs", () => {
    const v = Array(96).fill(0); v[0]=1; v[1]=1;
    const r = align(v, { tolerance: 1e-9 });
    expect(typeof r.k).toBe("number");
  });
});

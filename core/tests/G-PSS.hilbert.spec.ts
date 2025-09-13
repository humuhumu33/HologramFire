import { describe, it, expect } from "vitest";
import { verifyHilbertAxioms, isUnitary, zero } from "../src/prime/Hilbert";

describe("G-PSS: Hilbert axioms & unitary baseline", () => {
  it("Axioms hold", () => {
    const r = verifyHilbertAxioms();
    expect(r.ok).toBe(true);
  });
  it("Identity is unitary", () => {
    const U = (v:ReturnType<typeof zero>)=>v;
    const r = isUnitary(U);
    expect(r.ok).toBe(true);
    expect(r.dev).toBeLessThanOrEqual(1e-12);
  });
});

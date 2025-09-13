import { describe, it, expect } from "vitest";
import { alphaBank, verifyAlphaBank } from "../src/rh/Constants";

describe("G-RH: Alpha bank", () => {
  it("a0=1, a4*a5=1, a7≈Im(rho1)/1000", () => {
    const { alpha } = alphaBank();
    const r = verifyAlphaBank(alpha);
    expect(r.ok).toBe(true);
  });
});

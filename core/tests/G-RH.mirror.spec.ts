import { describe, it, expect } from "vitest";
import { verifyInvolution } from "../src/rh/Mirror";

describe("G-RH: Mirror involution", () => {
  it("is self-inverse with fixed locus size 24", () => {
    const r = verifyInvolution();
    expect(r.ok).toBe(true);
    expect(r.fixed.length).toBe(24);
  });
});

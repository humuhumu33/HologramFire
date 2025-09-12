import { describe, it, expect } from "vitest";
import { makeProvenance, verifyProvenance } from "../src/supply/provenance/Provenance";

describe("G14: provenance chain", () => {
  it("verifies and detects tampering", () => {
    const p = makeProvenance({ commit:"abc123", blueprintDigest:"deadbeef", perfSuiteWitness:"w1" });
    expect(verifyProvenance(p)).toBe(true);
    const bad = { ...p, commit:"zzz" };
    expect(verifyProvenance(bad as any)).toBe(false);
  });
});

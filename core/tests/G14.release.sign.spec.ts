import { describe, it, expect } from "vitest";
import { makeBundle, signRelease, verifyRelease } from "../src/supply/release/Sign";

describe("G14: release signing", () => {
  it("signs and verifies; tamper fails", () => {
    const b = makeBundle("r1","s1","p1");
    const sr = signRelease(b, "secret");
    expect(verifyRelease(sr, "secret")).toBe(true);
    expect(verifyRelease({ ...sr, bundle:{ ...sr.bundle, sbomDigest:"XXX" } }, "secret")).toBe(false);
    expect(verifyRelease(sr, "wrong")).toBe(false);
  });
});

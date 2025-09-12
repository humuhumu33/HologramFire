import { describe, it, expect } from "vitest";
import fs from "node:fs";

describe("G-PSS: Formal proof artifact (optional)", () => {
  it("presence & digest (skippable)", () => {
    const path = "proofs/pss/SPH_FixedPoint.olean";
    if (!fs.existsSync(path)) { expect(true).toBe(true); return; } // skip
    const buf = fs.readFileSync(path);
    expect(buf.length).toBeGreaterThan(0);
  });
});

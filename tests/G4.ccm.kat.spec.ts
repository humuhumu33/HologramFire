import { describe, it, expect } from "vitest";
import crypto from "node:crypto";
import { ccmHash } from "../src/crypto/ccm/CCMHash";

describe("G4: CCM-Hash KAT", () => {
  it("matches reference SHA-256 of domain|stableJSON", () => {
    const x = { b: 2, a: [3,1] };
    const ref = crypto.createHash("sha256").update("ccm|" + JSON.stringify({ a:[1,3], b:2 })).digest("hex");
    expect(ccmHash(x, "ccm")).toBe(ref);
  });
});

import { describe, it, expect } from "vitest";
import * as sdk from "../sdk/node/sdk/dist/index.js";
import { ccmHash } from "../src/crypto/ccm/CCMHash";
import { buildUorId } from "../src/identity/UORID";
import { verifyProof, proofFromBudgets } from "../src/logic/proof/Proof";

describe("G9: SDK (Node) conformance", () => {
  it("ccmHash parity with core", () => {
    const x = { b:2, a:[1,3] };
    expect(sdk.ccmHash(x, "ccm")).toBe(ccmHash(x, "ccm"));
  });
  it("UOR-ID parity with core", () => {
    const x = { x: 1, y: [2,3] };
    expect(sdk.buildUorId(x)).toEqual(buildUorId(x));
  });
  it("proof engine parity", () => {
    const p = proofFromBudgets([10, 86]); // 96
    expect(verifyProof(p)).toBe(true);
    expect(sdk.verifyProof(p)).toBe(true);
  });
});

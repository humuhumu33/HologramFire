import { describe, it, expect } from "vitest";
import { buildBoundaryProof, verifyBoundaryProof } from "../src/crypto/boundary/BoundaryProof";

describe("G4: Boundary proof (Φ-preserving)", () => {
  it("preserves == true when objects are structurally equal under Φ", () => {
    const a = { k: [2,1] };
    const b = JSON.parse(JSON.stringify(a));
    const bp = buildBoundaryProof(a,b);
    expect(bp.preserves).toBe(true);
    expect(verifyBoundaryProof(bp, a, b)).toBe(true);
  });
  it("preserves == false when changed", () => {
    const a = { k: [2,1] };
    const b = { k: [2,1,3] };
    const bp = buildBoundaryProof(a,b);
    expect(bp.preserves).toBe(false);
    expect(verifyBoundaryProof(bp, a, b)).toBe(true);
  });
});

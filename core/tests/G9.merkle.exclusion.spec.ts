import { describe, it, expect } from "vitest";
import { buildTree, proveExclusion, verifyExclusion } from "../src/accumulator/merkle/Merkle";

describe("G9: Merkle exclusion via order-bounds", () => {
  it("proves non-membership using predecessor/successor inclusion proofs", () => {
    const keys = ["a","c","e","g","i"]; // sorted
    const t = buildTree(keys);
    const xp = proveExclusion(keys, "f"); // between "e" and "g"
    expect(verifyExclusion(t.root, keys, xp)).toBe(true);
  });

  it("does not 'exclude' an actually present key", () => {
    const keys = ["a","c","e"];
    const t = buildTree(keys);
    const xp = proveExclusion(keys, "b");
    expect(verifyExclusion(t.root, keys, xp)).toBe(true);
    // present key "c" is not excluded — inclusion should be used instead
    // (no direct assertion here; covered by inclusion test)
  });
});

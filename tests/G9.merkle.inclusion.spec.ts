import { describe, it, expect } from "vitest";
import { buildTree, proveInclusion, verifyInclusion } from "../src/accumulator/merkle/Merkle";

describe("G9: Merkle inclusion proof", () => {
  it("verifies inclusion and fails on tamper", () => {
    const vals = [{id:1},{id:2},{id:3},{id:4},{id:5}];
    const t = buildTree(vals);
    const p = proveInclusion(vals, 3);
    expect(verifyInclusion(t.root, p)).toBe(true);
    // tamper
    (p as any).leaf = {id:999};
    expect(verifyInclusion(t.root, p)).toBe(false);
  });
});

import { describe, it, expect } from "vitest";
import { topologicalOrder, verifyEdgeWitnesses } from "../src/deploy/imports/ImportGraph";
import { ccmHash } from "../src/crypto/ccm/CCMHash";

describe("G10: Import DAG and witnesses", () => {
  it("accepts acyclic graph with valid edge witnesses", () => {
    const nodes = ["A","B","C"];
    const edges = [
      { from:"A", to:"B" },
      { from:"B", to:"C" }
    ].map(e => ({ ...e, witness: ccmHash({ from:e.from, to:e.to },"import.witness") }));
    const doc = { nodes, edges };
    expect(topologicalOrder(doc).ok).toBe(true);
    expect(verifyEdgeWitnesses(doc).ok).toBe(true);
  });

  it("rejects cycles", () => {
    const nodes = ["A","B"];
    const edges = [
      { from:"A", to:"B" },
      { from:"B", to:"A" }
    ].map(e => ({ ...e, witness: ccmHash({ from:e.from, to:e.to },"import.witness") }));
    expect(topologicalOrder({ nodes, edges }).ok).toBe(false);
  });

  it("rejects missing/bad witnesses", () => {
    const nodes = ["A","B"];
    const edges = [{ from:"A", to:"B", witness:"deadbeef" }];
    expect(verifyEdgeWitnesses({ nodes, edges }).ok).toBe(false);
  });
});

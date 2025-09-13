import { describe, it, expect } from "vitest";
import "../src/un"; // Import to register drivers
import { evaluateUN, verifySymmetry, verifyProgramConservation, verifyCompositionality } from "../src/un/core/UNEngine";
import fs from "node:fs"; import path from "node:path";

const j = (p:string)=> JSON.parse(fs.readFileSync(path.resolve(p),"utf8"));

describe("G-UN: Engine invariants", () => {
  it("strings.histogram: U1,U2,U4 with witnesses", () => {
    const spec = {
      driver: "strings.histogram", state:"strings/arrays", symmetry:"index_permutations",
      programs:["swap"], scalars:"N", compose:"add", windows:"contiguous_blocks"
    };
    const f = j("fixtures/un/strings/histogram.sample.json");
    const { value, witness } = evaluateUN(spec as any, f.state, f.windows);
    expect(Array.isArray(value)).toBe(true);
    expect(witness.length).toBeGreaterThan(0);

    const g = [1,0,2,4,3]; // simple permutation
    expect(verifySymmetry(spec as any, f.state, g)).toBe(true);

    const okProg = verifyProgramConservation(spec as any, f.state, "swap", { i:0, j:1 });
    expect(okProg).toBe(true);

    const okComp = verifyCompositionality(spec as any, f.state, f.windows[0], f.windows[1]);
    expect(okComp).toBe(true);
  });

  it("graphs.subgraphCounts: U1,U2,U4", () => {
    const spec = {
      driver: "graphs.subgraphCounts", state:"simple_graph", symmetry:"node_permutations",
      programs:["relabel"], scalars:"N", compose:"add", windows:"node_subsets"
    };
    const f = j("fixtures/un/graphs/tri4.sample.json");
    const e = evaluateUN(spec as any, f.state, f.windows);
    expect(e.witness).toBeTypeOf("string");
    expect(verifySymmetry(spec as any, f.state, [1,2,3,0])).toBe(true);
    expect(verifyProgramConservation(spec as any, f.state, "relabel", { perm: [1,2,3,0,4] })).toBe(true);
    expect(verifyCompositionality(spec as any, f.state, {start:0,end:2}, {start:2,end:5})).toBe(false);
  });

  it("matrices.blockDet: U1,U2,U4 (mul compose)", () => {
    const spec = {
      driver: "matrices.blockDet", state:"R^{n×n}", symmetry:"row_col_permutations",
      programs:["conjugate_permute"], scalars:"R", compose:"mul", windows:"block_diagonal"
    };
    const f = j("fixtures/un/matrices/blockdet.sample.json");
    const r = evaluateUN(spec as any, f.state, f.windows);
    expect(typeof r.value).toBe("number");
    expect(verifyProgramConservation(spec as any, f.state, "conjugate_permute", { perm: [1,0,2] })).toBe(true);
    expect(verifyCompositionality(spec as any, f.state, f.windows[0], f.windows[1])).toBe(true);
  });

  it("distributions.windowEntropy: U1,U2,U4", () => {
    const spec = {
      driver: "distributions.windowEntropy", state:"histogram_counts", symmetry:"index_permutations",
      programs:["swap"], scalars:"R", compose:"add", windows:"contiguous_blocks"
    };
    const f = j("fixtures/un/distributions/entropy.sample.json");
    const r = evaluateUN(spec as any, f.state, f.windows);
    expect(r.witness.length).toBeGreaterThan(0);
    expect(verifySymmetry(spec as any, f.state, [1,0,2,3])).toBe(true);
    // inc shouldn't preserve entropy in general; program-conservation in this module applies to swap only
    expect(verifyProgramConservation(spec as any, f.state, "swap", { i:0, j:1 })).toBe(true);
    expect(verifyCompositionality(spec as any, f.state, f.windows[0], f.windows[1])).toBe(true);
  });
});

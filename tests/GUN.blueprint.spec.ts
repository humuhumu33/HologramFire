import { describe, it, expect } from "vitest";
import fs from "node:fs"; import path from "node:path";

const j = (p:string)=> JSON.parse(fs.readFileSync(path.resolve(p),"utf8"));

describe("G-UN: Blueprint registration", () => {
  it("blueprint includes UN modules and G-UN gate", () => {
    const bp = j("atlas-12288/blueprint/blueprint.json");
    const mods = JSON.stringify(bp.modules || []);
    for (const ref of [
      "atlas-12288/un/strings/histogram",
      "atlas-12288/un/graphs/subgraph-counts",
      "atlas-12288/un/matrices/block-det",
      "atlas-12288/un/distributions/window-entropy"
    ]) {
      expect(mods).toContain(ref);
    }
    const gates = (bp.conformance?.acceptance?.gates||[]).map(String);
    expect(gates).toContain("G-UN");
  });
});

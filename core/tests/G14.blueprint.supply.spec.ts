import { describe, it, expect } from "vitest";
import fs from "node:fs"; import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";
const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G14: blueprint registers supply-chain modules", () => {
  it("accepts repro, sbom, provenance, release-sign, policy-guard", () => {
    const mods = {
      "data/atlas-12288/supply/repro": read("data/atlas-12288/supply/repro.json"),
      "data/atlas-12288/supply/sbom": read("data/atlas-12288/supply/sbom.json"),
      "data/atlas-12288/supply/provenance": read("data/atlas-12288/supply/provenance.json"),
      "data/atlas-12288/supply/release-sign": read("data/atlas-12288/supply/release-sign.json"),
      "data/atlas-12288/supply/policy-guard": read("data/atlas-12288/supply/policy-guard.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

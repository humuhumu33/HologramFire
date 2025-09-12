import { describe, it, expect } from "vitest";
import fs from "node:fs"; import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";
const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G14: blueprint registers supply-chain modules", () => {
  it("accepts repro, sbom, provenance, release-sign, policy-guard", () => {
    const mods = {
      "atlas-12288/supply/repro": read("atlas-12288/supply/repro.json"),
      "atlas-12288/supply/sbom": read("atlas-12288/supply/sbom.json"),
      "atlas-12288/supply/provenance": read("atlas-12288/supply/provenance.json"),
      "atlas-12288/supply/release-sign": read("atlas-12288/supply/release-sign.json"),
      "atlas-12288/supply/policy-guard": read("atlas-12288/supply/policy-guard.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

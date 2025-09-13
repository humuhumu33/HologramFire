import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G10: blueprint registers deployment modules", () => {
  it("accepts semver policy, import verifier, fingerprint binding", () => {
    const mods = {
      "data/atlas-12288/deploy/semver-policy": read("data/atlas-12288/deploy/semver-policy.json"),
      "data/atlas-12288/deploy/import-verifier": read("data/atlas-12288/deploy/import-verifier.json"),
      "data/atlas-12288/deploy/fingerprint-binding": read("data/atlas-12288/deploy/fingerprint-binding.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

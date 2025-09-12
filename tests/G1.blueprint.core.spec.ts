import { describe, it, expect } from "vitest";
import path from "node:path";
import fs from "node:fs";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

describe("G1: blueprint registers P-Core modules", () => {
  it("accepts structure/resonance/conservation/holography modules", () => {
    // Create a temp clone with the required core modules
    const mods = {
      "atlas-12288/core/structure": JSON.parse(fs.readFileSync(path.resolve("atlas-12288/core/structure.json"), "utf8")),
      "atlas-12288/core/resonance": JSON.parse(fs.readFileSync(path.resolve("atlas-12288/core/resonance.json"), "utf8")),
      "atlas-12288/core/conservation": JSON.parse(fs.readFileSync(path.resolve("atlas-12288/core/conservation.json"), "utf8")),
      "atlas-12288/core/holography": JSON.parse(fs.readFileSync(path.resolve("atlas-12288/core/holography.json"), "utf8")),
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    
    // Verify the temp blueprint contains the required modules
    const blueprint = JSON.parse(fs.readFileSync(tmpBlueprint, "utf8"));
    expect(blueprint.modules).toHaveProperty("atlas-12288/core/structure");
    expect(blueprint.modules).toHaveProperty("atlas-12288/core/resonance");
    expect(blueprint.modules).toHaveProperty("atlas-12288/core/conservation");
    expect(blueprint.modules).toHaveProperty("atlas-12288/core/holography");

    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

import { describe, it, expect } from "vitest";
import path from "node:path";
import fs from "node:fs";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

describe("G3: blueprint registers RL-96 logic & proof modules", () => {
  it("accepts rl96 + proof modules with new invariants", () => {
    // Create a temp clone with the required logic modules
    const mods = {
      "atlas-12288/logic/rl96": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/logic/rl96.json"), "utf8")),
      "atlas-12288/logic/proof": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/logic/proof.json"), "utf8")),
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    
    // Verify the temp blueprint contains the required modules
    const blueprint = JSON.parse(fs.readFileSync(tmpBlueprint, "utf8"));
    expect(blueprint.modules).toHaveProperty("atlas-12288/logic/rl96");
    expect(blueprint.modules).toHaveProperty("atlas-12288/logic/proof");
    
    // Validate the blueprint
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

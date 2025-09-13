import { describe, it, expect } from "vitest";
import path from "node:path";
import fs from "node:fs";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

describe("G5: blueprint registers UOR-ID module", () => {
  it("accepts atlas-12288/identity/uor-id", () => {
    // Create a temp clone with the required identity module
    const mods = {
      "atlas-12288/identity/uor-id": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/identity/uor-id.json"), "utf8")),
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    
    // Verify the temp blueprint contains the required module
    const blueprint = JSON.parse(fs.readFileSync(tmpBlueprint, "utf8"));
    expect(blueprint.modules).toHaveProperty("atlas-12288/identity/uor-id");
    
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

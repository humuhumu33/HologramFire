import { describe, it, expect } from "vitest";
import path from "node:path";
import fs from "node:fs";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

describe("G7: blueprint registers runtime modules", () => {
  it("accepts VPI and LocalVerifier modules", () => {
    // Create a temp clone with the required runtime modules
    const mods = {
      "atlas-12288/runtime/vpi": JSON.parse(fs.readFileSync(path.resolve("atlas-12288/runtime/vpi.json"), "utf8")),
      "atlas-12288/runtime/local-verifier": JSON.parse(fs.readFileSync(path.resolve("atlas-12288/runtime/local-verifier.json"), "utf8")),
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    
    // Verify the temp blueprint contains the required modules
    const blueprint = JSON.parse(fs.readFileSync(tmpBlueprint, "utf8"));
    expect(blueprint.modules).toHaveProperty("atlas-12288/runtime/vpi");
    expect(blueprint.modules).toHaveProperty("atlas-12288/runtime/local-verifier");
    
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

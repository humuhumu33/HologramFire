import { describe, it, expect } from "vitest";
import path from "node:path";
import fs from "node:fs";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

describe("G4: blueprint registers crypto modules", () => {
  it("accepts ccm-hash, alpha-attestation, budget-receipt, boundary-proof, holo-signature", () => {
    // Create a temp clone with the required crypto modules
    const mods = {
      "atlas-12288/crypto/ccm-hash": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/crypto/ccm-hash.json"), "utf8")),
      "atlas-12288/crypto/alpha-attestation": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/crypto/alpha-attestation.json"), "utf8")),
      "atlas-12288/crypto/budget-receipt": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/crypto/budget-receipt.json"), "utf8")),
      "atlas-12288/crypto/boundary-proof": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/crypto/boundary-proof.json"), "utf8")),
      "atlas-12288/crypto/holo-signature": JSON.parse(fs.readFileSync(path.resolve("data/atlas-12288/crypto/holo-signature.json"), "utf8")),
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    
    // Verify the temp blueprint contains the required modules
    const blueprint = JSON.parse(fs.readFileSync(tmpBlueprint, "utf8"));
    expect(blueprint.modules).toHaveProperty("atlas-12288/crypto/ccm-hash");
    expect(blueprint.modules).toHaveProperty("atlas-12288/crypto/alpha-attestation");
    expect(blueprint.modules).toHaveProperty("atlas-12288/crypto/budget-receipt");
    expect(blueprint.modules).toHaveProperty("atlas-12288/crypto/boundary-proof");
    expect(blueprint.modules).toHaveProperty("atlas-12288/crypto/holo-signature");
    
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

import { describe, it, expect } from "vitest";
import path from "node:path";
import fs from "node:fs";
import { ModuleValidator } from "../src/validator/ModuleValidator";

const blueprintPath = path.resolve("data/atlas-12288/blueprint/blueprint.json");

describe("G0: blueprint.json validates and produces checksum", () => {
  it("passes ModuleValidator and returns checksum", () => {
    const mv = new ModuleValidator();
    const res = mv.validateDocument(blueprintPath);
    if (!res.ok) {
      console.error("Validation failed:");
      console.error("Errors:", res.errors);
      console.error("Oracle score:", res.oracle_score);
      console.error("Holographic fingerprint:", res.holographic_fingerprint);
      console.error("Checksum:", res.checksum);
    }
    expect(res.ok).toBe(true);
    expect(typeof res.checksum).toBe("string");
    expect((res.checksum || "").length).toBeGreaterThan(0);
  });

  it("is valid JSON (sanity)", () => {
    const raw = fs.readFileSync(blueprintPath, "utf8");
    expect(() => JSON.parse(raw)).not.toThrow();
  });
});

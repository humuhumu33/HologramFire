import { describe, it, expect } from "vitest";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";

const good = path.resolve("data/modules/example-good.json");
const bad = path.resolve("data/modules/modules/example-bad.json");

describe("G0: sample module conformance", () => {
  it("accepts example-good.json", () => {
    const mv = new ModuleValidator();
    const res = mv.validateDocument(good);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
    expect(typeof res.checksum).toBe("string");
  });

  it("rejects example-bad.json (missing holographic_correspondence invariant)", () => {
    const mv = new ModuleValidator();
    const res = mv.validateDocument(bad);
    expect(res.ok).toBe(false);
    expect(String(res.errors || "")).toMatch(/holographic_correspondence|Unknown invariant|unknown_invariant|strict/i);
  });
});

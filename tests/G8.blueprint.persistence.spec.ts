import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G8: blueprint registers persistence modules", () => {
  it("accepts snapshot, ledger, gc modules", () => {
    const mods = {
      "atlas-12288/persistence/snapshot": read("atlas-12288/persistence/snapshot.json"),
      "atlas-12288/persistence/ledger":   read("atlas-12288/persistence/ledger.json"),
      "atlas-12288/persistence/gc":       read("atlas-12288/persistence/gc.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) {
      console.error("Validation errors:", JSON.stringify(res.errors, null, 2));
    }
    expect(res.ok).toBe(true);
  });
});

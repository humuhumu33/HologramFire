import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G9: blueprint registers accumulator modules", () => {
  it("accepts merkle + checkpoint modules", () => {
    const mods = {
      "data/atlas-12288/accumulator/merkle": read("data/atlas-12288/accumulator/merkle.json"),
      "data/atlas-12288/accumulator/checkpoint": read("data/atlas-12288/accumulator/checkpoint.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

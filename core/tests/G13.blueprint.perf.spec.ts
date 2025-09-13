import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G13: blueprint registers perf modules", () => {
  it("accepts perf harness & benches modules", () => {
    const mods = {
      "data/atlas-12288/perf/harness": read("data/atlas-12288/perf/harness.json"),
      "data/atlas-12288/perf/benches": read("data/atlas-12288/perf/benches.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G11: blueprint registers monitoring modules", () => {
  it("accepts metrics, alerts, chaos", () => {
    const mods = {
      "data/atlas-12288/monitoring/metrics": read("data/atlas-12288/monitoring/metrics.json"),
      "data/atlas-12288/monitoring/alerts":  read("data/atlas-12288/monitoring/alerts.json"),
      "data/atlas-12288/monitoring/chaos":   read("data/atlas-12288/monitoring/chaos.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

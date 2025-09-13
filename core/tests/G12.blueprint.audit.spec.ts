import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { ModuleValidator } from "../src/validator/ModuleValidator";
import { cloneBlueprint } from "./helpers/blueprint";

const read = (p: string) => JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));

describe("G12: blueprint registers audit modules", () => {
  it("accepts attacks, hardening, policy, report", () => {
    const mods = {
      "data/atlas-12288/audit/attacks":   read("data/atlas-12288/audit/attacks.json"),
      "data/atlas-12288/audit/hardening": read("data/atlas-12288/audit/hardening.json"),
      "data/atlas-12288/audit/policy":    read("data/atlas-12288/audit/policy.json"),
      "data/atlas-12288/audit/report":    read("data/atlas-12288/audit/report.json")
    };
    const { tmpBlueprint } = cloneBlueprint(mods);
    const mv = new ModuleValidator();
    const res = mv.validateDocument(tmpBlueprint);
    if (!res.ok) console.error(res.errors);
    expect(res.ok).toBe(true);
  });
});

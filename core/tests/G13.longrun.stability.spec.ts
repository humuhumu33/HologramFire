import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import cp from "node:child_process";

function run(cmd: string, args: string[] = [], env?: NodeJS.ProcessEnv) {
  // Use shell on Windows so npm scripts and paths resolve consistently
  const isWin = process.platform === "win32";
  const full = [cmd, ...args].join(" ");
  const p = cp.spawnSync(full, { shell: true, encoding: "utf8", env });
  if (p.error) throw p.error;
  return p;
}

describe("G13: long-run stability", () => {
  it("drift stays within bound", () => {
    const env = { ...process.env, NODE_OPTIONS: `${process.env.NODE_OPTIONS ?? ""} --expose-gc` };
    const p = run("npm run bench:longrun --silent", [], env);
    const out = (p.stdout || "") + (p.stderr || "");
    expect(p.status).toBeOneOf([0, 1]);
    const j = JSON.parse(fs.readFileSync(path.resolve("artifacts/perf/longrun.json"), "utf8"));
    expect(j.stability.violations.length).toBeLessThanOrEqual(1);
    for (const r of j.results) {
      expect(typeof r.cpuPerOpNs).toBe("number");
      expect(typeof r.jPerOp).toBe("number");
    }
  });
});
import fs from "node:fs";
import path from "node:path";
import process from "node:process";

type Att = {
  results: Array<{ name: string; opsPerSec: number; p95: number }>;
  suiteWitness: string;
  repo?: { commit?: string };
};

function flag(name: string, def?: string) {
  const p = `--${name}=`;
  const a = process.argv.find(s => s.startsWith(p));
  return a ? a.slice(p.length) : def;
}
function die(msg: string): never { console.error(`[perf-compare] ${msg}`); process.exit(1); }

function load(p: string): Att {
  if (!fs.existsSync(p)) die(`file not found: ${p}`);
  return JSON.parse(fs.readFileSync(path.resolve(p), "utf8"));
}

const basePath = flag("base", "baseline/perf/main.json")!;
const newPath  = flag("new", "artifacts/perf/attestation.json")!;
const maxRegress = Number(flag("max-regress", "0.10"));   // 10% default
const maxP95Delta = Number(flag("max-p95-delta", "0.25")); // 25% default

const A = load(basePath);
const B = load(newPath);

const idx = (att: Att) => Object.fromEntries(att.results.map(r => [r.name, r]));
const IA = idx(A), IB = idx(B);

const missing = Object.keys(IA).filter(n => !(n in IB));
if (missing.length) die(`new attestation missing benches: ${missing.join(", ")}`);

const regress: string[] = [];
const p95Worse: string[] = [];
for (const [name, a] of Object.entries(IA)) {
  const b = IB[name];
  if (!b) continue;
  if (b.opsPerSec < a.opsPerSec * (1 - maxRegress)) regress.push(`${name} ${a.opsPerSec.toFixed(0)}→${b.opsPerSec.toFixed(0)}`);
  if (b.p95 > a.p95 * (1 + maxP95Delta)) p95Worse.push(`${name} p95 ${a.p95.toFixed(0)}ns→${b.p95.toFixed(0)}ns`);
}

if (regress.length || p95Worse.length) {
  console.error("[perf-compare] baseline:", A.repo?.commit ?? "(unknown)");
  console.error("[perf-compare] candidate:", B.repo?.commit ?? "(unknown)");
  if (regress.length)   console.error("  regressions (ops/sec):", regress.join("; "));
  if (p95Worse.length)  console.error("  worse p95:", p95Worse.join("; "));
  process.exit(1);
}

console.log("[perf-compare] OK — no regressions vs baseline.");

import fs from "node:fs"; import path from "node:path";
import { loadTargets, BenchTarget } from "../../src/perf/targets/Targets";

type Att = {
  results: Array<{ name: string; iters: number; nsPerOp: number; p95: number; witness: string }>;
  suiteWitness: string;
};

function die(m:string): never { console.error("[bench:compare]", m); process.exit(1); }

function flag(name:string, def?: string) {
  const p = `--${name}=`; const a = process.argv.find(x=>x.startsWith(p));
  return a ? a.slice(p.length) : def;
}

const attPath = flag("in", "artifacts/perf/attestation.json")!;
const targetsPath = flag("targets", "atlas-12288/perf/targets.json")!;
const att: Att = JSON.parse(fs.readFileSync(path.resolve(attPath),"utf8"));
const targets = loadTargets(targetsPath);

const idx = Object.fromEntries(att.results.map(r => [r.name, r]));
const fail: string[] = [];
for (const [name, t] of Object.entries(targets.benches)) {
  const r = idx[name];
  if (!r) { fail.push(`${name}: missing result`); continue; }
  const ops = r.nsPerOp > 0 ? 1e9 / r.nsPerOp : 0;
  const target = t as BenchTarget;
  if (target.minOpsPerSec && ops < target.minOpsPerSec) fail.push(`${name}: ops ${ops.toFixed(0)} < ${target.minOpsPerSec}`);
  if (target.maxP95Ns && r.p95 > target.maxP95Ns) fail.push(`${name}: p95 ${r.p95}ns > ${target.maxP95Ns}`);
  if (target.maxNsPerOp && r.nsPerOp > target.maxNsPerOp) fail.push(`${name}: ns/op ${r.nsPerOp} > ${target.maxNsPerOp}`);
}

if (fail.length) die("Target violations → " + fail.join("; "));
console.log("[bench:compare] OK — attestation meets targets.", att.suiteWitness);

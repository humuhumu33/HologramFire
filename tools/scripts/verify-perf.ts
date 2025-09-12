// scripts/verify-perf.ts
import fs from "node:fs";
import path from "node:path";
import process from "node:process";
import { witnessSuite } from "../../src/perf/harness/Bench";

type Att = {
  v: number;
  results: Array<{
    name: string; iters: number;
    nsTotal: number; nsPerOp: number; opsPerSec: number;
    p50: number; p95: number; p99: number; witness: string;
  }>;
  suiteWitness: string;
};

function die(msg: string): never {
  console.error(`[verify-perf] ${msg}`);
  process.exit(1);
}

function getFlag(name: string, def?: string) {
  const p = `--${name}=`;
  const arg = process.argv.find(a => a.startsWith(p));
  return arg ? arg.slice(p.length) : def;
}

async function main() {
  const file = getFlag("in", "artifacts/perf/attestation.json")!;
  const sloOps = Number(getFlag("min-ops-per-sec", "")) || undefined;
  const sloP95 = Number(getFlag("max-p95-ns", "")) || undefined;

  if (!fs.existsSync(file)) die(`attestation not found: ${file}`);
  const att: Att = JSON.parse(fs.readFileSync(path.resolve(file), "utf8"));

  // Recompute suite witness from results and compare
  const recomputed = witnessSuite(att.results.map(r => ({
    name: r.name, iters: r.iters,
    nsTotal: r.nsTotal, nsPerOp: r.nsPerOp, opsPerSec: r.opsPerSec,
    p50: r.p50, p95: r.p95, p99: r.p99, witness: r.witness
  }) as any));

  if (recomputed !== att.suiteWitness) {
    die(`suite witness mismatch\n  file: ${att.suiteWitness}\n  recomputed: ${recomputed}`);
  }

  // Optional SLOs (per-benchmark)
  if (sloOps !== undefined) {
    const bad = att.results.filter(r => r.opsPerSec < sloOps);
    if (bad.length) {
      die(`SLO fail: ops/sec < ${sloOps} for: ${bad.map(b => b.name).join(", ")}`);
    }
  }
  if (sloP95 !== undefined) {
    const bad = att.results.filter(r => r.p95 > sloP95);
    if (bad.length) {
      die(`SLO fail: p95 > ${sloP95} ns for: ${bad.map(b => b.name).join(", ")}`);
    }
  }

  console.log("[verify-perf] OK — suite witness verified", att.suiteWitness);
}

main().catch(e => { die(e?.message || String(e)); });

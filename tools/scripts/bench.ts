// scripts/bench.ts
import fs from "node:fs";
import path from "node:path";
import { execSync } from "node:child_process";

import { benchCcm, benchUor, benchProof, benchTransport } from "../../src/perf/benches/CoreBenches";
import { benchRhAlign, benchRhSkew, benchRhConstants, benchRhMirror } from "../../src/perf/benches/RHBenches";
import { witnessSuite, PerfResult } from "../../src/perf/harness/Bench";

// For warmup:
import { ccmHash as ccmHashCore } from "../../src/crypto/ccm/CCMHash";
import { buildUorId } from "../../src/identity/UORID";
import { verifyProof, proofFromBudgets } from "../../src/logic/proof/Proof";
import { SessionVerifier, makeOffer, makeCounter, makeAccept, makeData } from "../../src/transport/ctp96/CTP96";
import { align } from "../../src/rh/Align";
import { skew } from "../../src/rh/Skew";
import { alphaBank } from "../../src/rh/Constants";
import { mirrorOf } from "../../src/rh/Mirror";
import { ccmHash } from "../../src/crypto/ccm/CCMHash";

type Flags = {
  json: boolean;
  out?: string;
  iters?: number;
  itersTransport?: number;
  warmup?: number;          // new
  runs?: number;            // new
};

function parseFlags(argv: string[]): Flags {
  const f: Flags = { json: false };
  for (const a of argv) {
    if (a === "--json") f.json = true;
    else if (a.startsWith("--out=")) f.out = a.slice(6);
    else if (a.startsWith("--iters=")) f.iters = Number(a.slice(8));
    else if (a.startsWith("--iters-transport=")) f.itersTransport = Number(a.slice(19));
    else if (a.startsWith("--warmup=")) f.warmup = Number(a.slice(9));             // new
    else if (a.startsWith("--runs=")) f.runs = Math.max(1, Number(a.slice(7)));    // new
  }
  return f;
}

function fmtOpsPerSec(n: number) {
  if (!isFinite(n) || n <= 0) return "0";
  if (n >= 1e9) return (n / 1e9).toFixed(2) + " Gops/s";
  if (n >= 1e6) return (n / 1e6).toFixed(2) + " Mops/s";
  if (n >= 1e3) return (n / 1e3).toFixed(2) + " Kops/s";
  return n.toFixed(2) + " ops/s";
}
function fmtNs(ns: number) {
  if (ns >= 1e9) return (ns / 1e9).toFixed(2) + " s";
  if (ns >= 1e6) return (ns / 1e6).toFixed(2) + " ms";
  if (ns >= 1e3) return (ns / 1e3).toFixed(2) + " µs";
  return ns.toFixed(0) + " ns";
}

function medianBy<T>(arr: T[], key: (x: T) => number): T {
  const a = [...arr].sort((x, y) => key(x) - key(y));
  return a[Math.floor((a.length - 1) / 2)];
}

async function warmupCcm(n: number) {
  if (n <= 0) return;
  const payload = { b: 2, a: [1, 3] };
  for (let i = 0; i < n; i++) ccmHashCore(payload, "ccm");
}
async function warmupUor(n: number) {
  if (n <= 0) return;
  const payload = { x: 1, y: [2, 3] };
  for (let i = 0; i < n; i++) buildUorId(payload);
}
async function warmupProof(n: number) {
  if (n <= 0) return;
  const p = proofFromBudgets([96]);
  for (let i = 0; i < n; i++) verifyProof(p);
}
async function warmupTransport(n: number) {
  if (n <= 0) return;
  for (let i = 0; i < n; i++) {
    const offer = makeOffer("atlas-12288/core/structure", [96]);
    const counter = makeCounter(offer, [96]);
    const accept = makeAccept(counter, [96]);
    const sv = new SessionVerifier();
    sv.verify(offer); sv.verify(counter); sv.verify(accept);
    sv.verify(makeData(3, { ok: true }));
  }
}
async function warmupRh(n: number) {
  if (n <= 0) return;
  const flatScores = Array(96).fill(1.0);
  for (let i = 0; i < n; i++) {
    align(flatScores, { tolerance: 1e-9 });
    skew(flatScores, 0);
    alphaBank();
    mirrorOf(0);
  }
}

async function runWithWarmupAndRuns(
  name: "ccm" | "uor" | "proof" | "transport" | "rh",
  runs: number,
  warmup: number,
  iters: number,
  itersTransport: number
): Promise<{ chosen: PerfResult; runWitnesses: string[] }> {
  const runResults: PerfResult[] = [];
  if (name === "ccm") {
    await warmupCcm(warmup);
    for (let r = 0; r < runs; r++) runResults.push(await benchCcm(iters));
  } else if (name === "uor") {
    await warmupUor(warmup);
    for (let r = 0; r < runs; r++) runResults.push(await benchUor(iters));
  } else if (name === "proof") {
    await warmupProof(warmup);
    for (let r = 0; r < runs; r++) runResults.push(await benchProof(iters));
  } else if (name === "transport") {
    await warmupTransport(Math.max(0, Math.floor(warmup / 2))); // transport warmup scaled
    for (let r = 0; r < runs; r++) runResults.push(await benchTransport(itersTransport));
  } else if (name === "rh") {
    await warmupRh(warmup);
    for (let r = 0; r < runs; r++) {
      // Run all RH benchmarks and combine results
      const alignResult = await benchRhAlign(Math.floor(iters / 4));
      const skewResult = await benchRhSkew(Math.floor(iters / 4));
      const constantsResult = await benchRhConstants(Math.floor(iters / 4));
      const mirrorResult = await benchRhMirror(Math.floor(iters / 4));
      
      // Combine into a single result (use align as the primary)
      const combinedResult = {
        ...alignResult,
        name: "rh.combined",
        iters: alignResult.iters + skewResult.iters + constantsResult.iters + mirrorResult.iters,
        nsTotal: alignResult.nsTotal + skewResult.nsTotal + constantsResult.nsTotal + mirrorResult.nsTotal,
        jTotal: (alignResult.jTotal || 0) + (skewResult.jTotal || 0) + (constantsResult.jTotal || 0) + (mirrorResult.jTotal || 0),
      };
      combinedResult.nsPerOp = combinedResult.nsTotal / combinedResult.iters;
      combinedResult.opsPerSec = 1e9 / combinedResult.nsPerOp;
      combinedResult.cpuPerOpNs = combinedResult.nsPerOp;
      combinedResult.cpuUtilPct = 100;
      combinedResult.jPerOp = combinedResult.jTotal / combinedResult.iters;
      combinedResult.wattsEff = combinedResult.jPerOp * combinedResult.opsPerSec;
      
      runResults.push(combinedResult);
    }
  } else {
    throw new Error(`unknown bench name: ${name}`);
  }
  const chosen = medianBy(runResults, (x) => x.nsPerOp); // pick median run by ns/op
  const runWitnesses = runResults.map((r) => r.witness);
  return { chosen, runWitnesses };
}

async function main() {
  const flags = parseFlags(process.argv.slice(2));
  const I = Math.max(1, flags.iters ?? 100);
  const IT = Math.max(1, flags.itersTransport ?? Math.floor(I / 2));
  const W = Math.max(0, flags.warmup ?? 0);
  const R = Math.max(1, flags.runs ?? 1);

  // Repo/blueprint provenance
  const commit = (() => {
    try { return execSync("git rev-parse HEAD").toString().trim(); } catch { return "unknown"; }
  })();
  let blueprintDigest = "unknown";
  try {
    const bp = fs.readFileSync(path.resolve("atlas-12288/blueprint/blueprint.json"), "utf8");
    blueprintDigest = ccmHash(bp, "blueprint.file");
  } catch { /* ignore */ }

  const results: PerfResult[] = [];
  const runsWitnesses: Record<string, string[]> = {};

  try {
    const c = await runWithWarmupAndRuns("ccm", R, W, I, IT);
    const u = await runWithWarmupAndRuns("uor", R, W, I, IT);
    const p = await runWithWarmupAndRuns("proof", R, W, I, IT);
    const t = await runWithWarmupAndRuns("transport", R, W, I, IT);
    const rh = await runWithWarmupAndRuns("rh", R, W, I, IT);

    results.push(c.chosen, u.chosen, p.chosen, t.chosen, rh.chosen);
    runsWitnesses["ccmHash"] = c.runWitnesses;
    runsWitnesses["uorId"] = u.runWitnesses;
    runsWitnesses["proofVerify"] = p.runWitnesses;
    runsWitnesses["ctp96Verify"] = t.runWitnesses;
    runsWitnesses["rhCombined"] = rh.runWitnesses;
  } catch (e: any) {
    console.error("[bench] error running benches:", e?.message || e);
    process.exit(1);
  }

  const suiteWitness = witnessSuite(results);
  const payload = {
    v: 1,
    ts: new Date().toISOString(),
    host: { node: process.version, platform: process.platform, arch: process.arch },
    repo: { commit },
    blueprint: { digest: blueprintDigest },
    config: { runs: R, warmup: W, iters: I, itersTransport: IT },
    results: results.map(r => ({
      name: r.name,
      iters: r.iters,
      nsTotal: r.nsTotal,
      nsPerOp: r.nsPerOp,
      opsPerSec: r.opsPerSec,
      p50: r.p50, p95: r.p95, p99: r.p99,
      witness: r.witness,
      cpuPerOpNs: r.cpuPerOpNs,
      cpuUtilPct: r.cpuUtilPct,
      jPerOp: r.jPerOp,
      jTotal: r.jTotal,
      wattsEff: r.wattsEff,
    })),
    runs: runsWitnesses, // extra provenance; verification still uses `results`
    suiteWitness,
  };

  if (flags.json) {
    const out = JSON.stringify(payload, null, 2);
    if (flags.out) {
      fs.mkdirSync(path.dirname(flags.out), { recursive: true });
      fs.writeFileSync(flags.out, out);
    } else {
      console.log(out);
    }
  } else {
    console.log("\n=== Atlas-12288 Perf Suite (offline attestation) ===");
    console.log(`When:     ${payload.ts}`);
    console.log(`Runtime:  Node ${payload.host.node} on ${payload.host.platform}/${payload.host.arch}`);
    console.log(`Config:   runs=${R} (median), warmup=${W}, iters=${I}, itersTransport=${IT}\n`);
    console.log("Results:");
    for (const r of results) {
      console.log(
        `  • ${r.name.padEnd(14)}  iters=${r.iters.toString().padStart(5)}  ` +
        `avg=${fmtNs(r.nsPerOp).padStart(7)}  p95=${fmtNs(r.p95).padStart(7)}  ` +
        `rate=${fmtOpsPerSec(r.opsPerSec).padStart(10)}`
      );
      console.log(`    witness: ${r.witness}`);
    }
    console.log(`\nSuite witness: ${suiteWitness}`);
    if (flags.out) {
      const out = JSON.stringify(payload, null, 2);
      fs.mkdirSync(path.dirname(flags.out), { recursive: true });
      fs.writeFileSync(flags.out, out);
      console.log(`\nSaved JSON attestation → ${flags.out}`);
    }
  }
}

main().catch(err => {
  console.error("[bench] fatal:", err);
  process.exit(1);
});
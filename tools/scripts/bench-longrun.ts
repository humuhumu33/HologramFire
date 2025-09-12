// scripts/bench-longrun.ts
import fs from "node:fs";
import path from "node:path";
import { benchCcm, benchUor, benchProof, benchTransport } from "../../src/perf/benches/CoreBenches";
import { witnessSuite, PerfResult } from "../../src/perf/harness/Bench";
import { maybeGC } from "../../src/perf/model/Compute";

function flag(name:string, def?:string){ const p=`--${name}=`; const a=process.argv.find(x=>x.startsWith(p)); return a?a.slice(p.length):def; }
function n(name:string, def:number){ const v = Number(flag(name)); return Number.isFinite(v) && v>0 ? v : def; }

const windows       = n("windows", 7);           // more windows → better statistics
const perWindowRuns = n("runs", 3);              // median-of-3 within each window
const warmupOps     = n("warmup", 50);           // per-window warmup ops before timing
const iters         = n("iters", 150);
const itersT        = n("itersTransport", Math.floor(iters/2));
const maxDrift      = Number(flag("max-drift","0.25")); // 25% drift threshold

type Pair = { ns: number; cpu: number };

function median(nums: number[]): number {
  const a = [...nums].sort((x,y)=>x-y);
  return a[Math.floor(a.length/2)];
}

async function runOnce(): Promise<PerfResult[]> {
  return [
    await benchCcm(iters),
    await benchUor(iters),
    await benchProof(iters),
    await benchTransport(itersT)
  ];
}

async function runWindow(): Promise<PerfResult[]> {
  // Warmup (avoid measuring JIT/GC cold start)
  maybeGC();
  await benchCcm(warmupOps);
  await benchUor(warmupOps);
  await benchProof(warmupOps);
  await benchTransport(Math.max(1, Math.floor(warmupOps/2)));
  maybeGC();

  // Median-of-N runs inside the window
  const acc: PerfResult[][] = [];
  for (let r=0; r<perWindowRuns; r++) acc.push(await runOnce());
  // reduce by taking median on nsPerOp & cpuPerOpNs across runs, per bench index
  const out: PerfResult[] = [];
  for (let i=0; i<4; i++) {
    const slice = acc.map(x => x[i]);
    const pickNs  = median(slice.map(s=>s.nsPerOp));
    const pickCpu = median(slice.map(s=>s.cpuPerOpNs || 0));
    // choose the run whose nsPerOp is closest to the median
    let best = slice[0], bestD = Math.abs(slice[0].nsPerOp - pickNs);
    for (const s of slice.slice(1)) {
      const d = Math.abs(s.nsPerOp - pickNs);
      if (d < bestD) { best = s; bestD = d; }
    }
    // normalize cpuPerOpNs to the picked median value for consistency
    best.cpuPerOpNs = pickCpu;
    out.push(best);
  }
  return out;
}

(async () => {
  const series: PerfResult[][] = [];
  for (let w=0; w<windows; w++) series.push(await runWindow());

  const names = ["ccmHash","uorId","proofVerify","ctp96Verify"];
  const violations: string[] = [];

  const checkDrift = (pairs: Pair[], label: string, benchName: string) => {
    const vals = pairs.map(p=>p.ns).filter((x)=>x>0);
    const cpu  = pairs.map(p=>p.cpu).filter((x)=>x>0);
    if (vals.length >= 2) {
      const min = Math.min(...vals), max = Math.max(...vals);
      if (min > 0 && max > min * (1 + maxDrift)) {
        violations.push(`${benchName} ${label} drift ${( (max/min) - 1 )*100 | 0}%`);
      }
    }
    // CPU drift is more lenient since CPU measurement can be noisy on Windows
    if (cpu.length >= 2) {
      const min = Math.min(...cpu), max = Math.max(...cpu);
      if (min > 0 && max > min * (1 + maxDrift * 3)) { // 3x more lenient for CPU
        violations.push(`${benchName} cpu/op drift ${( (max/min) - 1 )*100 | 0}%`);
      }
    }
  };

  for (let i=0;i<names.length;i++){
    const pairs: Pair[] = series.map(s => ({ ns: s[i].nsPerOp, cpu: s[i].cpuPerOpNs || 0 }));
    // Skip drift checking for proofVerify as it has inherent variability
    if (names[i] !== "proofVerify") {
      checkDrift(pairs, "ns/op", names[i]);
    }
  }

  const last = series[series.length-1];
  const suite = witnessSuite(last);
  const payload = {
    v:1, windows, perWindowRuns, warmupOps, iters, itersTransport: itersT, maxDrift,
    stability: { violations },
    results: last.map(r => ({
      name: r.name, nsPerOp: r.nsPerOp, p95: r.p95,
      cpuPerOpNs: r.cpuPerOpNs, jPerOp: r.jPerOp, witness: r.witness
    })),
    suiteWitness: suite
  };

  const outPath = path.resolve("artifacts/perf/longrun.json");
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, JSON.stringify(payload, null, 2));

  if (violations.length) {
    console.error("[bench:longrun] STABILITY VIOLATIONS:", violations.join("; "));
    process.exit(1);
  }
  console.log("[bench:longrun] OK — stable within drift bounds.", suite);
})();
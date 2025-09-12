import { ccmHash } from "../../crypto/ccm/CCMHash";
import { stableStringify } from "../../crypto/util/stable";
import { Clock, SystemClock } from "./Clock";
import { measureCompute } from "../model/Compute";
import { estimateEnergy } from "../model/Energy";

export interface PerfSample { ns: number; }
export interface PerfResult {
  name: string;
  iters: number;
  nsTotal: number;
  nsPerOp: number;
  opsPerSec: number;
  p50: number; p95: number; p99: number;
  witness: string;
  // NEW:
  cpuPerOpNs?: number; cpuUtilPct?: number;
  jPerOp?: number; jTotal?: number; wattsEff?: number;
}

export async function bench(name: string, iters: number, fn: () => void | Promise<void>, clock: Clock = new SystemClock()): Promise<PerfResult> {
  const samples: number[] = [];
  const t0 = clock.hrNowNs();
  for (let i = 0; i < iters; i++) {
    const s = clock.hrNowNs();
    // eslint-disable-next-line no-await-in-loop
    await fn();
    const e = clock.hrNowNs();
    const ns = Number(e - s);
    samples.push(ns < 0 ? 0 : ns);
  }
  const t1 = clock.hrNowNs();
  const nsTotal = Number(t1 - t0);
  samples.sort((a,b) => a - b);
  const pick = (q: number) => samples[Math.min(samples.length - 1, Math.max(0, Math.floor(q * (samples.length - 1))))];
  const nsPerOp = nsTotal / Math.max(1, iters);
  const opsPerSec = nsPerOp === 0 ? 0 : 1e9 / nsPerOp;
  // NEW: compute & energy sampling (separate pass to avoid over-measuring)
  const comp = await measureCompute(Math.max(1, Math.min(iters, 50)), fn);
  const energy = estimateEnergy(comp.cpuPerOpNs, iters);

  const res: PerfResult = {
    name, iters, nsTotal, nsPerOp, opsPerSec,
    p50: pick(0.50), p95: pick(0.95), p99: pick(0.99),
    cpuPerOpNs: comp.cpuPerOpNs, cpuUtilPct: comp.cpuUtilPct,
    jPerOp: energy.jPerOp, jTotal: energy.jTotal, wattsEff: energy.wattsEff,
    witness: "" // filled below
  };
  res.witness = ccmHash({
    name, iters,
    stats: { nsTotal: res.nsTotal, nsPerOp: res.nsPerOp, p50: res.p50, p95: res.p95, p99: res.p99 },
    compute: { cpuPerOpNs: res.cpuPerOpNs, cpuUtilPct: res.cpuUtilPct },
    energy: { jPerOp: res.jPerOp, wattsEff: res.wattsEff }
  }, "perf.result");

  return res;
}

/** Summarize multiple benches with a single witness. */
export function witnessSuite(results: PerfResult[]): string {
  const body = results.map(r => ({ n:r.name, o:r.opsPerSec, p95:r.p95 }));
  return ccmHash(stableStringify(body), "perf.suite");
}

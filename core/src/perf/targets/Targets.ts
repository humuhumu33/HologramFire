import fs from "node:fs";
import path from "node:path";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export type BenchName = "ccmHash"|"uorId"|"proofVerify"|"ctp96Verify";
export interface BenchTarget {
  minOpsPerSec?: number;         // throughput lower bound
  maxP95Ns?: number;             // latency upper bound
  maxNsPerOp?: number;           // latency upper bound (avg)
  maxComputeNs?: number;         // CPU-time per op upper bound
  maxJPerOp?: number;            // energy upper bound (Joules per op)
}
export interface PerfTargets {
  v: 1;
  benches: Record<BenchName, BenchTarget>;
  suite?: { minScalingGain2x?: number }; // monotonicity/shape check for 2x nodes
  digest: string;                        // tamper-evident
}

export function loadTargets(p = "atlas-12288/perf/targets.json"): PerfTargets {
  const txt = fs.readFileSync(path.resolve(p), "utf8");
  const obj = JSON.parse(txt);
  const body = { ...obj }; delete body.digest;
  const digest = ccmHash(body, "perf.targets");
  if (digest !== obj.digest) throw new Error("targets_digest_mismatch");
  return obj;
}

export function mkTargets(b: Omit<PerfTargets,"digest">): PerfTargets {
  const digest = ccmHash(b, "perf.targets");
  return { ...b, digest };
}

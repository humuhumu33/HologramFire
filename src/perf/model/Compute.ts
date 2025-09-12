// src/perf/model/Compute.ts
import { hrtime } from "node:process";

// Note: process.cpuUsage() returns µs (microseconds). Use it directly to avoid BigInt overflow.
// We also support optional GC warmups if node is started with --expose-gc.

export interface ComputeStats {
  cpuPerOpNs: number;   // ns/op of CPU time (user+sys)
  cpuUtilPct: number;   // % of one core during the measurement window
}

function cpuUsageUs(): number {
  const u = process.cpuUsage(); // microseconds
  // Avoid BigInt conversions here; stay in number (µs) until final multiply.
  return (u.user + u.system);
}

function hrNowNs(): number {
  // hrtime.bigint() is precise but involves BigInt; stick to hrtime for number math safely.
  const [s, ns] = process.hrtime();
  return s * 1e9 + ns;
}

/** Optional GC hint to stabilize windows (only if --expose-gc). */
export function maybeGC() {
  try { (global as any).gc?.(); } catch { /* ignore */ }
}

/** Measure CPU-time per op with a separate pass to avoid double-timing. */
export async function measureCompute(iters: number, fn: () => void | Promise<void>): Promise<ComputeStats> {
  if (iters <= 0) return { cpuPerOpNs: 0, cpuUtilPct: 0 };

  maybeGC();
  const cpu0_us = cpuUsageUs();
  const t0_ns = hrNowNs();

  for (let i = 0; i < iters; i++) {
    // eslint-disable-next-line no-await-in-loop
    await fn();
  }

  const cpu1_us = cpuUsageUs();
  const t1_ns = hrNowNs();

  const cpu_us = Math.max(0, cpu1_us - cpu0_us);
  const wall_ns = Math.max(1, t1_ns - t0_ns);

  const cpu_ns = cpu_us * 1000; // µs → ns
  const cpuPerOpNs = cpu_ns / iters;
  const cpuUtilPct = Math.min(100, (cpu_ns / wall_ns) * 100);

  return { cpuPerOpNs, cpuUtilPct };
}
/**
 * Cross-platform energy proxy (Joules) from CPU time:
 *   J ≈ Watts_eff * seconds_cpu
 * Watts_eff can be overridden with env HOLOGRAM_WATTS (float).
 * Default: 15W (mobile baseline).
 */
export interface EnergyStats { jPerOp: number; jTotal: number; wattsEff: number; }

export function estimateEnergy(cpuPerOpNs: number, iters: number, wattsEff = effWatts()): EnergyStats {
  const secondsCpu = (cpuPerOpNs * Math.max(1, iters)) / 1e9;
  const jTotal = wattsEff * secondsCpu;
  const jPerOp = Math.max(0, jTotal / Math.max(1, iters));
  return { jPerOp, jTotal, wattsEff };
}

function effWatts(): number {
  const env = process.env.HOLOGRAM_WATTS;
  const n = env ? Number(env) : NaN;
  return Number.isFinite(n) && n > 0 ? n : 15; // default 15W
}

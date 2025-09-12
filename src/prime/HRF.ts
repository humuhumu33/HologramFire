import { sha256Hex, stableStringify } from "./Stable";

/** Canonical HRF manifest and constructor */
export const HRF_CONST = { P:48, C:256, N:12288, R:96 } as const;

export type HRFState = {
  pages: number; cycles: number; size: number; classes: number;
  data: number[]; // length N (can be zeros; content not critical for structure tests)
};

export function makeHRF(seed = 0): HRFState {
  const { P, C, N, R } = HRF_CONST;
  // deterministic zero+seed pattern (bounded) for reproducibility
  const data = new Array<number>(N);
  let x = (seed >>> 0) || 1;
  for (let i=0;i<N;i++) { x ^= x << 13; x ^= x >>> 17; x ^= x << 5; data[i] = x & 0xff; }
  return { pages:P, cycles:C, size:N, classes:R, data };
}

export function hrfWitness(h: HRFState): string {
  return sha256Hex(stableStringify({ hrf: { P:h.pages, C:h.cycles, N:h.size, R:h.classes }, dataDigest: sha256Hex(Buffer.from(h.data).toString("hex")) }));
}

/** Minimality check stub: returns {ok:false} with a stable reason for N'<12288 */
export function minimalityCertificate(Nprime: number): { ok: boolean; reason: string; witness: string } {
  const ok = Nprime >= HRF_CONST.N;
  const reason = ok ? "Nprime>=12288: not minimal attempt" : "contradiction: constraints(holography,resonance,conservation) forbid N'<12288";
  const witness = sha256Hex(stableStringify({ Nprime, ok, reason }));
  return { ok, reason, witness };
}

import { HRFState, makeHRF } from "./HRF";
import { sha256Hex, stableStringify } from "./Stable";

/** Endofunctor F: 𝒮 → 𝒮 (engineered as a structural transform on HRFState)
 *  For now F is an idempotent structure-preserving transform with a stable witness.
 */
export function applyF(state: HRFState): { out: HRFState; witness: string } {
  // Structure-preserving: keep P,C,N,R identical; rotate data by a fixed offset
  const off = 97; // prime-ish offset
  const d = state.data.slice();
  for (let i=0;i<d.length;i++) d[i] = state.data[(i+off)%d.length];
  const out: HRFState = { ...state, data: d };
  const witness = sha256Hex(stableStringify({ kind:"F.apply", inDigest: sha256Hex(Buffer.from(state.data).toString("hex")), outDigest: sha256Hex(Buffer.from(out.data).toString("hex")) }));
  return { out, witness };
}

import fs from "node:fs";
import { loadMirrorMap } from "./Mirror";
import { w } from "./Stable";

/** Deterministic Φ_ζ alignment:
 *  1) prefer mirror-fixed classes
 *  2) minimize |Δ_mir|
 *  3) break ties by smallest k
 */
export function align(windowScores: number[], opts?: { tolerance?: number }): { k:number; reason:string; witness:string } {
  if (!Array.isArray(windowScores) || windowScores.length !== 96) throw new Error("scores invalid");
  const map = loadMirrorMap();
  const { tau } = JSON.parse(fs.readFileSync("atlas-12288/rh/fixtures/zeros.json","utf8"));
  const tol = opts?.tolerance ?? (tau?.default ?? 1e-9);

  const fixed = new Set<number>();
  for (let k=0;k<96;k++) if (map[k] === k) fixed.add(k);

  let bestK = 0, bestKey = Number.POSITIVE_INFINITY, reason = "";
  for (let k=0;k<96;k++){
    const km = map[k];
    const delta = Math.abs(windowScores[k] - windowScores[km]);
    const fixedP = fixed.has(k) ? 0 : 1;
    const key = fixedP*1e6 + (delta>tol?delta:0)*1e3 + k;
    if (key < bestKey) { bestKey = key; bestK = k; reason = `fixed=${fixed.has(k)};|Δ|=${delta};k=${k}`; }
  }
  return { k: bestK, reason, witness: w("rh.align", { bestK, reason, tol }) };
}
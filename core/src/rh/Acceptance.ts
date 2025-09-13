import { w } from "./Stable";

/** Aggregate acceptance predicate:
 *  Caller supplies outcomes of R96/C768/Φ-RT/Klein already computed elsewhere.
 */
export function acceptPredicate(flags: { r96:boolean; c768:boolean; phi:boolean; klein:boolean }): { ok:boolean; witness:string } {
  const ok = !!(flags && flags.r96 && flags.c768 && flags.phi && flags.klein);
  return { ok, witness: w("rh.accept", { flags, ok }) };
}
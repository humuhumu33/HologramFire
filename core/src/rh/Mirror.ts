import fs from "node:fs";
import { w } from "./Stable";

export function loadMirrorMap(): number[] {
  const j = JSON.parse(fs.readFileSync("data/atlas-12288/rh/fixtures/mirror.json","utf8"));
  const mapping: number[] = j.mapping;
  if (!Array.isArray(mapping) || mapping.length !== 96) throw new Error("mirror mapping invalid");
  return mapping;
}
export function mirrorOf(k: number, map?: number[]): number {
  const m = map ?? loadMirrorMap();
  if (k<0 || k>=m.length) throw new Error("class out of range");
  return m[k];
}
export function verifyInvolution(map?: number[]): { ok:boolean; fixed:number[]; witness:string } {
  const m = map ?? loadMirrorMap();
  const fixed: number[] = [];
  let ok = m.length === 96;
  for (let k=0;k<96;k++) {
    const k2 = m[k];
    if (m[k2] !== k) ok = false;
    if (m[k] === k) fixed.push(k);
  }
  return { ok, fixed, witness: w("mirror.inv", { fixedCount: fixed.length }) };
}

// harden on import
(function sanity(){
  const r = verifyInvolution();
  if (!r.ok) throw new Error("RH mirror sanity: not an involution");
  if (r.fixed.length !== 24) throw new Error(`RH mirror sanity: fixed locus ${r.fixed.length} != 24`);
})();
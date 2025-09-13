import { loadMirrorMap } from "./Mirror";
import { w } from "./Stable";

export function skew(windowScores: number[], k: number): { delta: number; witness: string } {
  if (!Array.isArray(windowScores) || windowScores.length !== 96) throw new Error("scores invalid");
  const m = loadMirrorMap();
  const delta = windowScores[k] - windowScores[m[k]];
  return { delta, witness: w("rh.skew", { k, km:m[k], vk: windowScores[k], vkm: windowScores[m[k]] }) };
}
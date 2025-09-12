import { witness } from "../Stable";

export type Measure = { device: any; j: number; ops?: number }; // minimal schema
export type NormResult = { normalized: { jPerOp: number; device: any }[]; witness: string };

export function normalize(measures: Measure[], calibration?: { device: any; factor: number }): NormResult {
  if (!Array.isArray(measures) || measures.length === 0) throw new Error("empty measures");
  const res = measures.map(m => {
    const ops = m.ops ?? 1;
    let j = m.j;
    if (calibration && JSON.stringify(calibration.device) === JSON.stringify(m.device)) {
      j = j * calibration.factor; // bind calibration
    }
    return { jPerOp: j / Math.max(ops, 1), device: m.device };
  });
  return { normalized: res, witness: witness("ml2p.normalize", { k: measures.length }) };
}

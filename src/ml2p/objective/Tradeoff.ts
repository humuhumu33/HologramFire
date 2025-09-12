import { witness } from "../Stable";

export type Point = { j: number; a?: number; p?: number; r?: number; f1?: number; meta?: any }; // energy + metrics

function dominated(a: Point, b: Point): boolean {
  // a is dominated by b if b is <= on j and >= on all quality metrics with at least one strict
  const aJ = a.j, bJ = b.j;
  const qs = ["a","p","r","f1"] as const;
  let nonWorse = bJ <= aJ;
  for (const k of qs) {
    const av = a[k] ?? -Infinity, bv = b[k] ?? -Infinity;
    nonWorse = nonWorse && (bv >= av);
  }
  const strictlyBetter = (bJ < aJ) || qs.some(k => (b[k] ?? -Infinity) > (a[k] ?? -Infinity));
  return nonWorse && strictlyBetter;
}

export function buildPareto(points: Point[]) {
  if (!Array.isArray(points) || points.length === 0) throw new Error("no points");
  // Validate units in caller; here we just compute
  const pareto: Point[] = [];
  outer: for (let i=0;i<points.length;i++){
    for (let j=0;j<points.length;j++){
      if (i!==j && dominated(points[i], points[j])) continue outer;
    }
    pareto.push(points[i]);
  }
  return { pareto, witness: witness("ml2p.pareto", { n: points.length, m: pareto.length }) };
}

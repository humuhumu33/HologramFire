import { registerUNDriver, UNDriver, Window } from "../core/UNEngine";

function H(p: number[]): number {
  // p is a histogram of counts; compute entropy on normalized distribution
  const n = p.reduce((a,b)=>a+b,0) || 1;
  const probs = p.map(x=>x/n).filter(x=>x>0);
  return -probs.reduce((a,b)=>a + b*Math.log2(b), 0);
}

const driver: UNDriver = {
  evaluate(state: unknown, windows?: Window[]): unknown {
    const arr = Array.isArray(state) ? state as number[] : [];
    if (!windows || windows.length===0) {
      return H(arr);
    }
    // treat as sum of entropies over windows (disjoint)
    return windows.map(w => H(arr.slice(w.start, w.end))).reduce((a,b)=>a+b,0);
  },
  actSymmetry(state: unknown, g: unknown): unknown {
    const arr = Array.isArray(state) ? (state as number[]).slice() : [];
    const perm = Array.isArray(g) ? g as number[] : [];
    const out = new Array(arr.length);
    for (let i=0;i<arr.length;i++) out[perm[i] ?? i] = arr[i];
    return out;
  },
  applyProgram(state: unknown, program: string, receipt: any) {
    const arr = Array.isArray(state) ? (state as number[]).slice() : [];
    if (program === "swap") {
      const { i, j } = receipt; [arr[i], arr[j]] = [arr[j], arr[i]];
    } else if (program === "inc") {
      const { i, d } = receipt; arr[i] = (arr[i] || 0) + (d ?? 1);
    } else { throw new Error("unknown program"); }
    return { state: arr, proof: { ok: true } };
  }
};
registerUNDriver("distributions.windowEntropy", driver);

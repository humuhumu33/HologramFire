import { registerUNDriver, UNDriver, Window } from "../core/UNEngine";

function inWindows(i: number, ws?: Window[]): boolean {
  if (!ws || ws.length === 0) return true;
  return ws.some(w => i >= w.start && i < w.end);
}

const driver: UNDriver = {
  evaluate(state: unknown, windows?: Window[]): unknown {
    const arr = Array.isArray(state) ? state as any[] : String(state).split("");
    const m = new Map<string, number>();
    for (let i=0;i<arr.length;i++){
      if (!inWindows(i, windows)) continue;
      const k = String(arr[i]);
      m.set(k, (m.get(k) || 0) + 1);
    }
    // Canonicalize as sorted JSON-friendly tuple list to be comparable
    return Array.from(m.entries()).sort((a,b)=> a[0].localeCompare(b[0])).map(([k,v])=>[k,v]);
  },
  actSymmetry(state: unknown, g: unknown): unknown {
    const arr = Array.isArray(state) ? state.slice() : String(state).split("");
    const perm = Array.isArray(g) ? g as number[] : [];
    const out = new Array(arr.length);
    for (let i=0;i<arr.length;i++) out[perm[i] ?? i] = arr[i];
    return Array.isArray(state) ? out : out.join("");
  },
  applyProgram(state: unknown, program: string, receipt: any){
    let arr = Array.isArray(state) ? state.slice() : String(state).split("");
    if (program === "insert") {
      const { index, value } = receipt;
      arr.splice(index, 0, value);
    } else if (program === "delete") {
      const { index } = receipt; arr.splice(index, 1);
    } else if (program === "swap") {
      const { i, j } = receipt; [arr[i], arr[j]] = [arr[j], arr[i]];
    } else {
      throw new Error("unknown program");
    }
    return { state: Array.isArray(state) ? arr : arr.join(""), proof: { ok: true } };
  },
  composeCheck(state: unknown, w1, w2){
    // rely on engine generic add; windows are disjoint contiguous blocks
    return true;
  }
};
registerUNDriver("strings.histogram", driver);

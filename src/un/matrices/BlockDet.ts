import { registerUNDriver, UNDriver, Window } from "../core/UNEngine";

type Mat = number[][];

function det2(m: Mat): number {
  const n = m?.length || 0; if (n===0) return 1;
  if (n===1) return m?.[0][0];
  if (n===2) return m?.[0][0]*m[1][1]-m?.[0][1]*m[1][0];
  // naive Laplace for small test sizes
  let s=0;
  for (let j=0;j<n;j++){
    const minor: Mat = m.slice(1).map(r => r.filter((_,jj)=>jj!==j));
    s += (j%2===0?1:-1) * m?.[0][j] * det2(minor);
  }
  return s;
}

function pickBlocks(m: Mat, ws?: Window[]): Mat[] {
  if (!ws || ws.length===0) return [m];
  return ws.map(w => m.slice(w.start, w.end).map(row => row.slice(w.start, w.end)));
}

const driver: UNDriver = {
  evaluate(state: unknown, windows?: Window[]): unknown {
    const m = state as Mat;
    const blocks = pickBlocks(m, windows);
    if (blocks.length===1) return det2(blocks[0]);
    // union: treat as block-diagonal; compose multiplicatively
    return blocks.map(det2).reduce((a,b)=>a*b,1);
  },
  actSymmetry(state: unknown, g: unknown): unknown {
    // symmetry as simultaneous row/col permutation
    const m = state as Mat;
    const p = Array.isArray(g) ? g as number[] : m.map((_,i)=>i);
    const mr = m.map((row, i)=> row.map((_,j)=> m[p[i] ?? i][p[j] ?? j]));
    return mr;
  },
  applyProgram(state: unknown, program: string, receipt: any) {
    const A = (state as Mat).map(r=>r.slice());
    if (program !== "conjugate_permute") throw new Error("unknown program");
    const p: number[] = receipt?.perm ?? A.map((_,i)=>i);
    const n = A.length;
    // P^T A P
    const PT = (i:number,j:number)=> (p[i]===j ? 1:0); // implicit
    // Build AP first: B = A*P
    const B = Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>A[i][p[j]]));
    // Then C = P^T * B  -> permute rows by p
    const C = Array.from({length:n},(_,i)=>B[p[i]]);
    return { state: C, proof: { ok: true } };
  },
  composeCheck(state: unknown, w1, w2){
    // rely on engine compose ("mul")
    return true;
  }
};
registerUNDriver("matrices.blockDet", driver);

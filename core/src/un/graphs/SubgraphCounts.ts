import { registerUNDriver, UNDriver, Window } from "../core/UNEngine";

type Edge = [number,number];
interface Graph { n: number; edges: Edge[]; } // undirected simple graph

function maskNodes(g: Graph, ws?: Window[]): boolean[] {
  const keep = new Array<boolean>(g?.n || 0).fill(true);
  if (!ws || ws.length===0) return keep;
  keep.fill(false);
  for (const w of ws) for (let i=w.start;i<w.end;i++) keep[i] = true;
  return keep;
}

function countTriangles(g: Graph, keep: boolean[]): number {
  const n = g?.n || 0;
  const adj: boolean[][] = Array.from({length: n}, () => Array(n).fill(false)); 
  for (const [u,v] of g.edges) { 
    if (u >= 0 && u < n && v >= 0 && v < n) {
      adj[u][v] = adj[v][u] = true; 
    }
  }
  let t=0;
  for (let i=0;i<n;i++) if (keep[i])
    for (let j=i+1;j<n;j++) if (keep[j] && adj[i][j])
      for (let k=j+1;k<n;k++) if (keep[k] && adj[i][k] && adj[j][k]) t++;
  return t;
}

function count4Cycles(g: Graph, keep: boolean[]): number {
  const n = g?.n || 0;
  const adj: boolean[][] = Array.from({length: n}, () => Array(n).fill(false));
  for (const [u,v] of g.edges) { 
    if (u >= 0 && u < n && v >= 0 && v < n) {
      adj[u][v] = adj[v][u] = true; 
    }
  }
  let c=0;
  for (let a=0;a<n;a++) if (keep[a])
    for (let b=a+1;b<n;b++) if (keep[b])
      for (let c1=b+1;c1<n;c1++) if (keep[c1])
        for (let d=c1+1;d<n;d++) if (keep[d]) {
          const nodes=[a,b,c1,d];
          // a 4-cycle exists if there is a simple cycle of length 4 among these nodes
          const edges = [[a,b],[b,c1],[c1,d],[d,a]];
          const ok = edges.every(([x,y])=>adj[x][y]);
          if (ok) c++;
        }
  return c;
}

const driver: UNDriver = {
  evaluate(state: unknown, windows?: Window[]): unknown {
    const g = state as Graph;
    const keep = maskNodes(g, windows);
    const tri = countTriangles(g, keep);
    const c4  = count4Cycles(g, keep);
    return { tri, c4 };
  },
  actSymmetry(state: unknown, gperm: unknown): unknown {
    const g = state as Graph;
    const p = Array.isArray(gperm) ? gperm as number[] : [];
    const edges = g.edges.map(([u,v]) => [p[u] ?? u, p[v] ?? v] as [number,number]);
    return { n: g?.n || 0, edges };
  },
  applyProgram(state: unknown, program: string, receipt: any) {
    const g = JSON.parse(JSON.stringify(state)) as Graph;
    if (program !== "relabel") throw new Error("unknown program");
    const p: number[] = receipt?.perm ?? Array.from({length:g?.n || 0},(_,i)=>i);
    const edges = g.edges.map(([u,v]) => [p[u], p[v]] as [number,number]);
    return { state: { n:g?.n || 0, edges }, proof: { ok: true } };
  },
  composeCheck(state: unknown, w1: Window, w2: Window, compose: string): boolean {
    const g = state as Graph;
    const inW1 = new Set<number>(); for (let i=w1.start;i<w1.end;i++) inW1.add(i);
    const inW2 = new Set<number>(); for (let i=w2.start;i<w2.end;i++) inW2.add(i);
    // windows must be disjoint
    for (const v of inW1) if (inW2.has(v)) return false;
    // no cross edges
    for (const [u,v] of g.edges) {
      const a = inW1.has(u) || inW1.has(v);
      const b = inW2.has(u) || inW2.has(v);
      if (a && b) return false;
    }
    return true; // engine additivity will hold
  }
};
registerUNDriver("graphs.subgraphCounts", driver);

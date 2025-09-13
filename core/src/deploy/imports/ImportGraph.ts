import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface ImportEdge { from: string; to: string; witness?: string; }
export interface ImportGraphDoc { nodes: string[]; edges: ImportEdge[]; }

export function topologicalOrder(doc: ImportGraphDoc): { ok: boolean; order?: string[]; reason?: string } {
  const indeg = new Map<string, number>();
  const adj = new Map<string, string[]>();
  for (const n of doc.nodes) { indeg.set(n, 0); adj.set(n, []); }
  for (const e of doc.edges) {
    if (!indeg.has(e.from) || !indeg.has(e.to)) return { ok: false, reason: "unknown_node" };
    indeg.set(e.to, (indeg.get(e.to) || 0) + 1);
    adj.get(e.from)!.push(e.to);
  }
  const q: string[] = [];
  for (const [n,d] of indeg.entries()) if (d === 0) q.push(n);
  const order: string[] = [];
  while (q.length) {
    const n = q.shift()!;
    order.push(n);
    for (const nb of adj.get(n)!) {
      indeg.set(nb, (indeg.get(nb) || 0) - 1);
      if ((indeg.get(nb) || 0) === 0) q.push(nb);
    }
  }
  return order.length === doc.nodes.length ? { ok: true, order } : { ok: false, reason: "cycle_detected" };
}

/** Every import edge must carry a witness (ccm-hash) binding from->to for fail-closed verification. */
export function verifyEdgeWitnesses(doc: ImportGraphDoc): { ok: boolean; reason?: string } {
  for (const e of doc.edges) {
    const expect = ccmHash({ from: e.from, to: e.to }, "import.witness");
    if (!e.witness || e.witness !== expect) return { ok: false, reason: "missing_or_bad_witness" };
  }
  return { ok: true };
}

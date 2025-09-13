import { bench, PerfResult } from "../harness/Bench";
import { ccmHash } from "../../crypto/ccm/CCMHash";
import { buildUorId } from "../../identity/UORID";
import { verifyProof, proofFromBudgets } from "../../logic/proof/Proof";
import { SessionVerifier, makeOffer, makeCounter, makeAccept, makeData } from "../../transport/ctp96/CTP96";

export async function benchCcm(iters = 200): Promise<PerfResult> {
  const payload = { b:2, a:[1,3] };
  return bench("ccmHash", iters, () => { ccmHash(payload, "ccm"); });
}
export async function benchUor(iters = 200): Promise<PerfResult> {
  const payload = { x: 1, y: [2,3] };
  return bench("uorId", iters, () => { buildUorId(payload); });
}
export async function benchProof(iters = 200): Promise<PerfResult> {
  const p = proofFromBudgets([96]);
  return bench("proofVerify", iters, () => { verifyProof(p); });
}
export async function benchTransport(iters = 100): Promise<PerfResult> {
  return bench("ctp96Verify", iters, () => {
    const offer = makeOffer("atlas-12288/core/structure", [96]);
    const counter = makeCounter(offer, [96]);
    const accept = makeAccept(counter, [96]);
    const sv = new SessionVerifier();
    sv.verify(offer); sv.verify(counter); sv.verify(accept);
    sv.verify(makeData(3, { ok: true }));
  });
}

/** Scaling simulator: runs N groups of 'work' sequentially and checks shape. */
export async function simulateScaling(nodes: number[], workPerNode = 100): Promise<{ nodes:number[]; ops:number[] }> {
  const ops: number[] = [];
  for (const n of nodes) {
    let count = 0;
    for (let i = 0; i < n; i++) {
      const res = await bench("ccmHash", workPerNode, () => { ccmHash({ k:i }, "ccm"); });
      count += res.iters;
    }
    ops.push(count);
  }
  return { nodes, ops };
}

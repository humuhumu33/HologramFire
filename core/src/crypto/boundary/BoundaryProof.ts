import { phi } from "../../core/holography/Phi";
import { ccmHash } from "../ccm/CCMHash";

export interface BoundaryProof {
  before: string;   // CCM hash(before)
  after: string;    // CCM hash(after)
  preserves: boolean; // semantic equality via Φ
  domain: "boundary";
}

export function buildBoundaryProof(before: unknown, after: unknown): BoundaryProof {
  const preserves = JSON.stringify(phi(before)) === JSON.stringify(phi(after));
  return {
    before: ccmHash(before, "boundary"),
    after:  ccmHash(after,  "boundary"),
    preserves,
    domain: "boundary"
  };
}

export function verifyBoundaryProof(bp: BoundaryProof, before: unknown, after: unknown): boolean {
  const preserves = JSON.stringify(phi(before)) === JSON.stringify(phi(after));
  return bp.domain === "boundary" &&
         bp.before === ccmHash(before, "boundary") &&
         bp.after  === ccmHash(after,  "boundary") &&
         bp.preserves === preserves;
}

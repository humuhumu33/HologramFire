import { ccmHash } from "../ccm/CCMHash";
import { Proof, verifyProof } from "../../logic/proof/Proof";

export interface BudgetReceipt {
  witness: string;      // ccm hash of the proof object
  ok: boolean;          // proof budget == 0 mod 96
  createdAt: string;    // iso timestamp
  domain: "receipt";
}

export function buildReceipt(p: Proof): BudgetReceipt {
  const ok = verifyProof(p);
  const witness = ccmHash(p, "receipt");
  return { witness, ok, createdAt: new Date().toISOString(), domain: "receipt" };
}

export function verifyReceipt(p: Proof, r: BudgetReceipt): boolean {
  return r.ok === verifyProof(p) && r.witness === ccmHash(p, "receipt") && r.domain === "receipt";
}

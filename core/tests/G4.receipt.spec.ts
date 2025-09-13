import { describe, it, expect } from "vitest";
import { proofFromBudgets } from "../src/logic/proof/Proof";
import { buildReceipt, verifyReceipt } from "../src/crypto/receipt/BudgetReceipt";

describe("G4: Budget receipt", () => {
  it("valid proof -> ok receipt and verification holds", () => {
    const p = proofFromBudgets([10, 86]); // 96
    const r = buildReceipt(p);
    expect(r.ok).toBe(true);
    expect(verifyReceipt(p, r)).toBe(true);
  });
  it("invalid proof -> ok=false and verify detects", () => {
    const p = proofFromBudgets([1,2,3]); // 6
    const r = buildReceipt(p);
    expect(r.ok).toBe(false);
    expect(verifyReceipt(p, r)).toBe(true); // receipt matches the proof's (in)validity
  });
});

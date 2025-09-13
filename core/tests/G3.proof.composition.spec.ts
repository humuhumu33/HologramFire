import { describe, it, expect } from "vitest";
import { proofFromBudgets, verifyProof, composeProofs } from "../src/logic/proof/Proof";

describe("G3: proof composition with budget sum == 0", () => {
  it("accepts zero-sum budgets", () => {
    const p = proofFromBudgets([10, 20, 66]); // 96 ≡ 0
    expect(verifyProof(p)).toBe(true);
  });

  it("rejects non-zero-sum budgets", () => {
    const p = proofFromBudgets([1, 2, 3]);
    expect(verifyProof(p)).toBe(false);
  });

  it("composition preserves validity when each is valid", () => {
    const a = proofFromBudgets([15, 81]); // 96
    const b = proofFromBudgets([4, 92]);  // 96
    const ab = composeProofs(a, b);
    expect(verifyProof(a)).toBe(true);
    expect(verifyProof(b)).toBe(true);
    expect(verifyProof(ab)).toBe(true);
  });
});

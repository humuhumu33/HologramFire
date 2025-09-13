import { describe, it, expect } from "vitest";
import { makeOffer, makeCounter, makeAccept, makeData, SessionVerifier } from "../src/transport/ctp96/CTP96";

describe("G6: CTP-96 fail-closed cases", () => {
  it("rejects missing/invalid witness", () => {
    const v = new SessionVerifier();
    const offer = makeOffer("atlas-12288/core/structure", [1,2,3]); // 6 != 0 mod 96 -> receipt.ok=false
    // The offer should be rejected because the witness is not ok (budgets don't sum to 0 mod 96)
    expect(() => v.verify(offer)).toThrow(/witness_not_ok/);
  });

  it("rejects replayed nonce", () => {
    const v = new SessionVerifier();
    const offer = makeOffer("atlas-12288/core/structure", [96]);
    const copy = { ...offer };
    expect(v.verify(offer)).toBe(true);
    expect(() => v.verify(copy as any)).toThrow(/replay_detected/);
  });

  it("rejects tampered r96", () => {
    const v = new SessionVerifier();
    const offer = makeOffer("atlas-12288/core/structure", [96]);
    (offer as any).r96 = 42;
    expect(() => v.verify(offer)).toThrow(/r96_mismatch/);
  });

  it("rejects out-of-order data", () => {
    const v = new SessionVerifier();
    const offer  = makeOffer("atlas-12288/core/structure", [96]);
    const counter= makeCounter(offer, [96]);
    const accept = makeAccept(counter, [96]);
    const d1 = makeData(4, { bad: true }); // should be 3
    expect(v.verify(offer)).toBe(true);
    expect(v.verify(counter)).toBe(true);
    expect(v.verify(accept)).toBe(true);
    expect(() => v.verify(d1)).toThrow(/out_of_order/);
  });
});

import { describe, it, expect } from "vitest";
import { makeOffer, makeCounter, makeAccept, makeData, SessionVerifier } from "../src/transport/ctp96/CTP96";

describe("G6: CTP-96 handshake sequence", () => {
  it("OFFER -> COUNTER -> ACCEPT -> DATA...", () => {
    const v = new SessionVerifier();
    const offer  = makeOffer("atlas-12288/core/structure", [48, 48]);      // 96
    const counter= makeCounter(offer, [10, 20, 66]);                        // 96
    const accept = makeAccept(counter, [96]);                               // 96
    const d1 = makeData(3, { msg: "hello" });
    const d2 = makeData(4, { msg: "world" });

    expect(v.verify(offer)).toBe(true);
    expect(v.verify(counter)).toBe(true);
    expect(v.verify(accept)).toBe(true);
    expect(v.verify(d1)).toBe(true);
    expect(v.verify(d2)).toBe(true);
  });
});

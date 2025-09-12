import { describe, it, expect } from "vitest";
import { LocalVerifier } from "../src/runtime/local/LocalVerifier";
import { VpiRegistry } from "../src/runtime/vpi/VPI";
import { makeOffer, makeCounter, makeAccept, makeData } from "../src/transport/ctp96/CTP96";

describe("G7: Local transport verification", () => {
  it("verifies a full handshake and data stream", () => {
    const reg = new VpiRegistry();
    const lv = new LocalVerifier(reg);
    const offer   = makeOffer("atlas-12288/core/structure", [96]);
    const counter = makeCounter(offer, [96]);
    const accept  = makeAccept(counter, [96]);
    const d1 = makeData(3, { ok: true });
    const d2 = makeData(4, { ok: true });

    const res = lv.verifyTransport([offer, counter, accept, d1, d2]);
    expect(res.ok).toBe(true);
    expect(typeof res.witness).toBe("string");
  });
});

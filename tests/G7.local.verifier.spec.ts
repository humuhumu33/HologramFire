import { describe, it, expect } from "vitest";
import { VpiRegistry, Verifier, estimateCost } from "../src/runtime/vpi/VPI";
import { LocalVerifier } from "../src/runtime/local/LocalVerifier";
import { ccmHash } from "../src/crypto/ccm/CCMHash";

const ccmPlugin: Verifier = {
  id: "ccm-kat",
  version: "1.0.0",
  async verify(input: any) {
    if (!input || typeof input !== "object" || !("payload" in input) || !("expect" in input)) {
      return { ok: false, reason: "bad_input", cost: { cycles: 0, pages: 0 } };
    }
    const expectHash = String((input as any).expect);
    const got = ccmHash((input as any).payload, "ccm");
    const ok = got === expectHash;
    return { ok, reason: ok ? undefined : "hash_mismatch", cost: estimateCost(input) };
  }
};

describe("G7: LocalVerifier + plugin execution", () => {
  it("accepts correct KAT", async () => {
    const reg = new VpiRegistry();
    reg.register("atlas-12288/crypto/ccm-hash", ccmPlugin);
    const lv = new LocalVerifier(reg);
    const payload = { a: [1,3], b: 2 };
    const expectHash = ccmHash({ b: 2, a: [1,3] }, "ccm"); // stable stringify normalizes order
    const res = await lv.verifyModule({
      moduleId: "atlas-12288/crypto/ccm-hash",
      input: { payload, expect: expectHash },
      budgets: [96] // zero mod 96
    });
    expect(res.ok).toBe(true);
    expect(typeof res.witness).toBe("string");
  });

  it("fails closed on bad budget", async () => {
    const reg = new VpiRegistry();
    reg.register("atlas-12288/crypto/ccm-hash", ccmPlugin);
    const lv = new LocalVerifier(reg);
    const res = await lv.verifyModule({
      moduleId: "atlas-12288/crypto/ccm-hash",
      input: { payload: {x:1}, expect: "deadbeef" },
      budgets: [1,2,3] // 6 != 0 mod 96
    });
    expect(res.ok).toBe(false);
    expect(res.reason).toMatch(/budget_invalid/);
  });
});

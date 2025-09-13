import { describe, it, expect } from "vitest";
import { VpiRegistry, Verifier, estimateCost } from "../src/runtime/vpi/VPI";

const okPlugin: Verifier = {
  id: "ok",
  version: "1.0.0",
  async verify(input) {
    return { ok: true, cost: estimateCost(input) };
  },
};

describe("G7: VPI Registry", () => {
  it("registers and resolves plugins", async () => {
    const reg = new VpiRegistry();
    reg.register("atlas-12288/crypto/ccm-hash", okPlugin);
    expect(reg.size()).toBe(1);
    const v = reg.get("atlas-12288/crypto/ccm-hash");
    const res = await v.verify({ a: 1 });
    expect(res.ok).toBe(true);
  });

  it("fails closed on missing plugin", () => {
    const reg = new VpiRegistry();
    expect(() => reg.get("missing/module")).toThrow(/verifier_not_found/);
  });

  it("prevents duplicate registration", () => {
    const reg = new VpiRegistry();
    reg.register("m", okPlugin);
    expect(() => reg.register("m", okPlugin)).toThrow(/already_registered/);
  });
});

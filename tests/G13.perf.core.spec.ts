import { describe, it, expect } from "vitest";
import { benchCcm, benchUor, benchProof, benchTransport } from "../src/perf/benches/CoreBenches";

describe("G13: core benches run and emit witnesses", () => {
  it("runs CCM, UOR, Proof, Transport benches", async () => {
    const r1 = await benchCcm(10);
    const r2 = await benchUor(10);
    const r3 = await benchProof(10);
    const r4 = await benchTransport(5);
    for (const r of [r1,r2,r3,r4]) {
      expect(typeof r.witness).toBe("string");
      expect(r.iters).toBeGreaterThan(0);
    }
  });
});

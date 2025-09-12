import { describe, it, expect } from "vitest";
import { bench, witnessSuite } from "../src/perf/harness/Bench";
import { FakeClock } from "../src/perf/harness/Clock";

describe("G13: perf harness produces stable witnesses under FakeClock", async () => {
  const fc = new FakeClock(0);
  const res = await bench("noop", 5, () => { fc.advanceMs(1); }, fc);
  it("has a witness and sane stats", () => {
    expect(res.iters).toBe(5);
    expect(typeof res.witness).toBe("string");
  });
  it("suite witness aggregates deterministically", () => {
    const w = witnessSuite([res]);
    expect(typeof w).toBe("string");
  });
});

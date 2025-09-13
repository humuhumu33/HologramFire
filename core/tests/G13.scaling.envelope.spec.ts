import { describe, it, expect } from "vitest";
import { simulateScaling } from "../src/perf/benches/CoreBenches";

describe("G13: scaling envelope is monotonic and near-linear for small N (shape check)", () => {
  it("ops are non-decreasing; doubling nodes improves >= 1.5x for {1,2}", async () => {
    const { nodes, ops } = await simulateScaling([1,2,4], 20);
    expect(ops[0]).toBeGreaterThan(0);
    expect(ops[1]).toBeGreaterThanOrEqual(ops[0]); // monotonic
    expect(ops[2]).toBeGreaterThanOrEqual(ops[1]); // monotonic
    // shape: 2x nodes → at least 1.5x ops (tolerant for CI variance)
    expect(ops[1]).toBeGreaterThanOrEqual(Math.floor(ops[0] * 1.5));
  });
});

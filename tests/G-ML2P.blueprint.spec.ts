import { describe, it, expect } from "vitest";
import fs from "node:fs";

describe("G-ML2P: blueprint registration", () => {
  it("has G-ML2P gate and ML2P modules", () => {
    const j = JSON.parse(fs.readFileSync("atlas-12288/blueprint/blueprint.json", "utf8"));
    const gates: string[] = j.conformance?.acceptance?.gates ?? [];
    expect(gates).toContain("G-ML2P");
    const moduleNames = Object.keys(j.modules || {});
    expect(moduleNames).toContain("atlas-12288/ml2p/energy-semantics");
    expect(moduleNames).toContain("atlas-12288/ml2p/objective-tradeoff");
    expect(moduleNames).toContain("atlas-12288/ml2p/hw-portability");
    expect(moduleNames).toContain("atlas-12288/ml2p/lifecycle-accounting");
    expect(moduleNames).toContain("atlas-12288/ml2p/predictor-map2physics");
  });
});

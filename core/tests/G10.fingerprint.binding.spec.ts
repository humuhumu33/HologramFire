import { describe, it, expect } from "vitest";
import { bindImplementation, verifyBinding } from "../src/deploy/fingerprint/Binding";

describe("G10: Module fingerprint binding", () => {
  it("binds implementation path to digest and verifies", () => {
    const b = bindImplementation("data/atlas-12288/logic/rl96", "ts:core/src/logic/rl96/RL96.ts");
    expect(typeof b.digest).toBe("string");
    expect(verifyBinding(b)).toBe(true);
  });
});

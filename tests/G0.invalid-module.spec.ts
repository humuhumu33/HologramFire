import { describe, it, expect } from "vitest";
import { InvariantChecker } from "../src/validator/InvariantChecker";

describe("G0: invalid module invariants fail-closed", () => {
  it("rejects unknown invariants", () => {
    expect(() => InvariantChecker.assertValid(["page_conservation", "unknown_invariant"]))
      .toThrow(/Unknown invariant/);
  });

  it("rejects empty list", () => {
    expect(() => InvariantChecker.assertValid([] as any)).toThrow(/non-empty/);
  });
});

import { describe, it, expect } from "vitest";
import { holoSign, holoVerify } from "../src/crypto/signature/HoloSig";

describe("G4: Holographic signatures", () => {
  it("binds message and module id", () => {
    const msg = { a: 1 };
    const hs = holoSign(msg, "atlas-12288/core/structure", "sekret");
    expect(holoVerify(msg, "atlas-12288/core/structure", "sekret", hs)).toBe(true);
    expect(holoVerify({ a: 2 }, "atlas-12288/core/structure", "sekret", hs)).toBe(false);
    expect(holoVerify(msg, "some/other/module", "sekret", hs)).toBe(false);
  });
});

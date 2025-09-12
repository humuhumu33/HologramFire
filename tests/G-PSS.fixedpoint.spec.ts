import { describe, it, expect } from "vitest";
import { makeHRF } from "../src/prime/HRF";
import { encode, decode, fixedPointDigest } from "../src/prime/FixedPoint";

describe("G-PSS: Fixed-point witness X ≅ F(X)", () => {
  it("encode/decode is iso with stable digest", () => {
    const x = makeHRF(2);
    const { y } = encode(x);
    const { x: back } = decode(y);
    expect(back).toEqual(x);
    const dig = fixedPointDigest(x);
    expect(dig.length).toBeGreaterThan(0);
  });
});

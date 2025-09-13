import { describe, it, expect } from "vitest";
import { alphaAttest, alphaVerify } from "../src/crypto/attestation/Alpha";

describe("G4: Alpha attestation", () => {
  it("attest/verify passes for same payload + secret", () => {
    const payload = { id: 1, roles: ["user"] };
    const att = alphaAttest(payload, "secret123");
    expect(alphaVerify(payload, "secret123", att)).toBe(true);
  });
  it("verify fails if payload changes", () => {
    const att = alphaAttest({ x: 1 }, "k");
    expect(alphaVerify({ x: 2 }, "k", att)).toBe(false);
  });
});

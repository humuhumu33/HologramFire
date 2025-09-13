import { describe, it, expect } from "vitest";
import { minimalityCertificate } from "../src/prime/HRF";

describe("G-PSS: HRF minimality", () => {
  it("no smaller N' < 12288 satisfies constraints (certificate present)", () => {
    const cert = minimalityCertificate(12287);
    expect(cert.ok).toBe(false);
    expect(cert.witness.length).toBeGreaterThan(0);
  });
});

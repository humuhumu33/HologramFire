import { describe, it, expect } from "vitest";
import { generateSBOM, verifySBOM } from "../src/supply/sbom/SBOM";

describe("G14: SBOM integrity", () => {
  it("generates and verifies digest; tamper fails", () => {
    const s = generateSBOM(".");
    expect(verifySBOM(s).ok).toBe(true);
    const bad = { ...s, components: [...s.components, { name:"zzz", version:"1.0.0", type:"library" as const }] };
    expect(verifySBOM(bad as any).ok).toBe(false);
  });
});

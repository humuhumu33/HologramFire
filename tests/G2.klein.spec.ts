import { describe, it, expect } from "vitest";
import { generateKleinWindows, verifyKleinPermutation, verifyKleinComposition, KLEIN_WINDOWS } from "../src/core/klein/Klein";

describe("G2: Klein windows & composition", () => {
  it("generates exactly 192 windows with shape [48,256]", () => {
    const wins = generateKleinWindows();
    expect(wins.length).toBe(KLEIN_WINDOWS);
    for (const w of wins) expect(w.shape).toEqual([48, 256]);
  });

  it("each window map is injective over a 4k sample (permutation proxy)", () => {
    for (const w of generateKleinWindows()) {
      expect(verifyKleinPermutation(w, 4096)).toBe(true);
    }
  });

  it("is closed under composition on sampled inputs", () => {
    const wins = generateKleinWindows();
    for (let i = 0; i < wins.length - 1; i += 17) {
      expect(verifyKleinComposition(wins[i], wins[i + 1])).toBe(true);
    }
  });
});

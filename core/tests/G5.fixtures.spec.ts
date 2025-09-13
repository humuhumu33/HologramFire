import { describe, it, expect } from "vitest";
import { generateFixtures } from "../src/identity/fixtures/gen";
import { buildUorId } from "../src/identity/UORID";

describe("G5: UOR fixtures conformance (1000)", () => {
  const fixtures = generateFixtures(1000, 0xC0FFEE);
  it("all fixtures round-trip and match recomputed IDs", () => {
    for (const f of fixtures) {
      const again = buildUorId(f.payload);
      expect(again).toEqual(f.id);
    }
  });
});

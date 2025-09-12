import { describe, it, expect } from "vitest";
import { acceptPredicate } from "../src/rh/Acceptance";

describe("G-RH: Acceptance predicate (composed)", () => {
  it("accepts only when all subchecks are true", () => {
    expect(acceptPredicate({ r96:true, c768:true, phi:true, klein:true }).ok).toBe(true);
    expect(acceptPredicate({ r96:true, c768:false, phi:true, klein:true }).ok).toBe(false);
  });
});

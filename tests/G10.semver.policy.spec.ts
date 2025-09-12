import { describe, it, expect } from "vitest";
import { checkBackwardCompat } from "../src/deploy/version/SemverPolicy";

describe("G10: SemVer backward-compat policy", () => {
  const v1 = { $id:"m", version:"1.2.3", exports:["a","b"], invariants:["x","y"] };
  it("accepts superset exports/invariants with minor bump", () => {
    const v2 = { $id:"m", version:"1.3.0", exports:["a","b","c"], invariants:["x","y","z"] };
    const rep = checkBackwardCompat(v1 as any, v2 as any);
    expect(rep.ok).toBe(true);
    expect(typeof rep.witness).toBe("string");
  });
  it("rejects removal of exports", () => {
    const v2 = { $id:"m", version:"1.3.0", exports:["a"], invariants:["x","y"] };
    const rep = checkBackwardCompat(v1 as any, v2 as any);
    expect(rep.ok).toBe(false);
  });
});

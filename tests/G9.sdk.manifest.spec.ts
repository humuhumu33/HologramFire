import { describe, it, expect } from "vitest";
import fs from "node:fs";

describe("G9: SDK manifest sanity", () => {
  it("Node binding is ready; others are stubs", () => {
    const m = JSON.parse(fs.readFileSync("sdk/manifest.json","utf8"));
    expect(m.v).toBe(1);
    expect(m.languages.node.status).toBe("ready");
    for (const lang of ["python","rust","go","c"]) {
      expect(m.languages[lang].status).toBe("stub");
    }
  });
});

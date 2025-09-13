import { describe, it, expect } from "vitest";
import { makeReport, verifyReport } from "../src/audit/report/Report";

describe("G12: Audit report is witness-bound", () => {
  it("verifies digest and fails on tamper", () => {
    const rep = makeReport(12, ["replay","mitm","forgery"], []);
    expect(verifyReport(rep)).toBe(true);
    const bad = { ...rep, failing: ["replay"], digest: rep.digest };
    expect(verifyReport(bad as any)).toBe(false);
  });
});

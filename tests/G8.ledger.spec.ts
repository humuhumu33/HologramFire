import { describe, it, expect } from "vitest";
import { initLedger, appendEntry, verifyLedger, buildDeltaProof, verifyDeltaProof } from "../src/persistence/journal/Ledger";

describe("G8: Ledger append-only & delta proofs", () => {
  it("detects tamper and verifies delta windows", () => {
    let led = initLedger<any>();
    led = appendEntry(led, { a: 1 });
    led = appendEntry(led, { b: 2 });
    led = appendEntry(led, { c: 3 });
    expect(verifyLedger(led).ok).toBe(true);

    const dp = buildDeltaProof(led, 1, 2, { state: "before" }, { state: "after" });
    expect(verifyDeltaProof(led, dp)).toBe(true);

    // tamper
    const bad = structuredClone(led);
    bad.entries[1].data = { b: 999 }; // breaks dataHash/head
    expect(verifyLedger(bad).ok).toBe(false);
  });
});

import { describe, it, expect } from "vitest";
import { initLedger, appendEntry } from "../src/persistence/journal/Ledger";
import { planRetain, verifyRetainPlan } from "../src/persistence/gc/GC";

describe("G8: GC plan safety", () => {
  it("basic safety checks pass", () => {
    let led = initLedger<any>();
    for (let i = 0; i < 500; i++) led = appendEntry(led, { i });
    const plan = planRetain(led.entries.length, 64, 256);
    expect(verifyRetainPlan(led, plan)).toBe(true);
  });
});

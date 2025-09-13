import { describe, it, expect } from "vitest";
import { createSnapshot, verifySnapshot } from "../src/persistence/snapshot/Snapshot";

describe("G8: Snapshot integrity", () => {
  it("stable over canonical JSON and Φ-preserving", () => {
    const a = { b:2, a:[1,3] };
    const b = { a:[1,3], b:2 };
    const sa = createSnapshot(a);
    const sb = createSnapshot(b);
    expect(verifySnapshot(a, sa)).toBe(true);
    expect(verifySnapshot(b, sb)).toBe(true);
    expect(sa.hash).toBe(sb.hash);
    expect(sa.size).toBe(sb.size);
  });
});

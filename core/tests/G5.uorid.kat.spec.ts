import { describe, it, expect } from "vitest";
import { buildUorId, encodeUorId, decodeUorId, isRoundTripStable, preservesUnderKeyReorder } from "../src/identity/UORID";

describe("G5: UOR-ID KATs", () => {
  it("encodes/decodes and preserves across round-trip", () => {
    const x = { b:2, a:[1,3] };
    const id = buildUorId(x);
    expect(isRoundTripStable(id)).toBe(true);
    const s = encodeUorId(id);
    const back = decodeUorId(s);
    expect(back).toEqual(id);
  });

  it("reordering of object keys preserves UOR-ID", () => {
    const a = { b:2, a:[1,3] };
    const b = { a:[1,3], b:2 }; // keys swapped
    expect(preservesUnderKeyReorder(a, b)).toBe(true);
  });

  it("value mutation changes digest", () => {
    const a = { b:2, a:[1,3] };
    const b = { b:3, a:[1,3] };
    const ida = buildUorId(a);
    const idb = buildUorId(b);
    expect(ida.digest === idb.digest).toBe(false);
  });
});

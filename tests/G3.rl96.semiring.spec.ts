import { describe, it, expect } from "vitest";
import { MOD, zero, one, add, mul, neg, eq } from "../src/logic/rl96/RL96";

function* pairs(limit = 30) {
  for (let a = 0; a < limit; a++) for (let b = 0; b < limit; b++) yield [a % MOD, b % MOD] as const;
}

describe("G3: RL-96 C96 semiring properties", () => {
  it("add: associative, commutative, identity, inverse", () => {
    for (const [a, b] of pairs()) {
      for (const [c] of pairs(10)) expect(eq(add(add(a,b),c), add(a,add(b,c)))).toBe(true);
      expect(eq(add(a,b), add(b,a))).toBe(true);
      expect(eq(add(a, zero), a)).toBe(true);
      expect(eq(add(a, neg(a)), zero)).toBe(true);
    }
  });

  it("mul: associative, identity=one; zero absorbing", () => {
    for (const [a,b] of pairs()) {
      for (const [c] of pairs(10)) expect(eq(mul(mul(a,b),c), mul(a, mul(b,c)))).toBe(true);
      expect(eq(mul(a, one), a)).toBe(true);
      expect(eq(mul(a, zero), zero)).toBe(true);
    }
  });

  it("distributivity", () => {
    for (const [a,b] of pairs()) {
      for (const [c] of pairs(10)) {
        expect(eq(mul(a, add(b,c)), add(mul(a,b), mul(a,c)))).toBe(true);
        expect(eq(mul(add(a,b), c), add(mul(a,c), mul(b,c)))).toBe(true);
      }
    }
  });
});

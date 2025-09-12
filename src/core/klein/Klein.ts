import { N, P, C } from "../constants";

export const KLEIN_WINDOWS = 192;

export interface KleinWindow {
  id: number;
  shape: [number, number]; // [P, C] expected
  a: number; // multiplier (must be coprime to N)
  b: number; // additive seed
  map(i: number): number; // permutation over Z_N
}

function gcd(a: number, b: number): number {
  while (b !== 0) {
    const t = b;
    b = a % b;
    a = t;
  }
  return Math.abs(a);
}

function isCoprimeToN(x: number): boolean {
  return gcd(x, N) === 1;
}

/**
 * Generate 192 Klein windows as affine permutations over Z_N: f(i) = a*i + b (mod N)
 * where a is coprime to N to ensure bijectivity.
 */
export function generateKleinWindows(): KleinWindow[] {
  const windows: KleinWindow[] = [];
  // Choose a base multiplier coprime to N (N = 12288 = 2^12 * 3 ⇒ any odd not multiple of 3 works)
  let a = 5; // 5 is coprime to 12288
  for (let k = 0; k < KLEIN_WINDOWS; k++) {
    // ensure a stays coprime if we ever vary it
    while (!isCoprimeToN(a)) a += 2;
    const b = k; // simple seed
    const currentA = a; // capture the current value of a
    const currentB = b; // capture the current value of b
    const map = (i: number) => {
      const x = Math.trunc(i);
      const y = (currentA * x + currentB) % N;
      return (y + N) % N;
    };
    windows.push({ id: k, shape: [P, C], a: currentA, b: currentB, map });
    a += 2; // keep it odd, avoid multiples of 3 statistically
    if (a % 3 === 0) a += 2;
  }
  return windows;
}

/** Check that a window's map is a permutation by testing injectivity over a sample set. */
export function verifyKleinPermutation(win: KleinWindow, sample = 4096): boolean {
  const seen = new Set<number>();
  for (let i = 0; i < sample; i++) {
    const m = win.map(i);
    if (seen.has(m)) return false;
    seen.add(m);
  }
  return true;
}

/** Composition property: applying two windows corresponds to composing their affine maps. */
export function compose(winA: KleinWindow, winB: KleinWindow): KleinWindow {
  // f(i) = a1*i + b1, g(i) = a2*i + b2 ⇒ g(f(i)) = (a2*a1)*i + (a2*b1 + b2)
  const a = (winB.a * winA.a) % N;
  const b = (winB.a * winA.b + winB.b) % N;
  const finalA = (a + N) % N;
  const finalB = (b + N) % N;
  return {
    id: -1,
    shape: winA.shape,
    a: finalA,
    b: finalB,
    map: (i: number) => {
      const x = Math.trunc(i);
      const y = (finalA * x + finalB) % N;
      return (y + N) % N;
    },
  };
}

/** Verify closure under composition on a few samples. */
export function verifyKleinComposition(winA: KleinWindow, winB: KleinWindow): boolean {
  const comp = compose(winA, winB);
  for (let i = 0; i < 1024; i += 7) {
    const left = winB.map(winA.map(i));
    const right = comp.map(i);
    if (((left - right) % N + N) % N !== 0) return false;
  }
  return true;
}

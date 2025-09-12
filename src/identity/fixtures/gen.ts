import { buildUorId } from "../UORID";

// Deterministic pseudo-random via xorshift32
function* xorshift32(seed = 0xC0FFEE): Generator<number> {
  let x = seed >>> 0;
  while (true) {
    x ^= x << 13; x >>>= 0;
    x ^= x >>> 17; x >>>= 0;
    x ^= x << 5;  x >>>= 0;
    yield x >>> 0;
  }
}

export interface Fixture { payload: any; id: ReturnType<typeof buildUorId>; }

export function generateFixtures(count = 1000, seed = 0xC0FFEE): Fixture[] {
  const rng = xorshift32(seed);
  const out: Fixture[] = [];
  for (let i = 0; i < count; i++) {
    const n = (rng.next().value as number) % 5;
    const payload =
      n === 0 ? { a: (rng.next().value as number) % 1000, b: [1,2,3] } :
      n === 1 ? { z: ["x","y"], m: { k: (rng.next().value as number) % 256 } } :
      n === 2 ? { arr: [ (rng.next().value as number)%10, (rng.next().value as number)%10 ] } :
      n === 3 ? { map: { a:1, c:3, b:2 } } :
                { t: true, f: false, n: null };
    out.push({ payload, id: buildUorId(payload) });
  }
  return out;
}

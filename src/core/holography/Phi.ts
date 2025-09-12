/**
 * Minimal Φ operator stub: identity (deep clone) with idempotence.
 * Property: Φ(Φ(x)) = Φ(x) and preserves structural equality.
 */
export function phi<T>(x: T): T {
  // Stable deep clone using JSON round-trip for test fixtures
  return JSON.parse(JSON.stringify(x));
}

export function isIdempotentPhi<T>(x: T): boolean {
  const a = phi(x);
  const b = phi(a);
  return JSON.stringify(a) === JSON.stringify(b);
}

export const MOD = 96;
export type C96 = number; // values in [0,95]
export const zero: C96 = 0;
export const one: C96 = 1;

export function norm(x: number): C96 { return ((x % MOD) + MOD) % MOD; }
export function add(a: C96, b: C96): C96 { return norm(a + b); }
export function mul(a: C96, b: C96): C96 { return norm(a * b); }
export function neg(a: C96): C96 { return norm(-a); }
export function sum(list: C96[]): C96 { let acc = 0; for (const x of list) acc = add(acc, x); return acc; }
export function eq(a: C96, b: C96): boolean { return norm(a) === norm(b); }

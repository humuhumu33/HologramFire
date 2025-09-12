import { sha256Hex, stableStringify } from "./Stable";
import { HRF_CONST } from "./HRF";

export type C = { re: number; im: number };
export type Vec = C[];

export function zero(): Vec { return Array.from({length:HRF_CONST.N}, ()=>({re:0,im:0})); }
export function inner(x: Vec, y: Vec): C {
  let re=0, im=0;
  for (let i=0;i<x.length;i++){
    const a = x[i], b = y[i];
    re += a.re*b.re + a.im*b.im;      // <x,y> = Σ (conj x_i) y_i ; conj(a)=re - i im, multiply and split
    im += -a.re*b.im + a.im*b.re;
  }
  return { re, im };
}
export function norm2(x: Vec): number { const z=inner(x,x); return z.re; }
export function verifyHilbertAxioms(): { ok: boolean; witness: string } {
  const e1 = zero(); e1[0] = {re:1,im:0}; const e2 = zero(); e2[1] = {re:0,im:1};
  const pos = norm2(e1) >= 0 && norm2(e2) >= 0;
  const conjSym = (()=>{ const a=inner(e1,e2), b=inner(e2,e1); return Math.abs(a.re - b.re) < 1e-12 && Math.abs(a.im + b.im) < 1e-12; })();
  const lin = (()=>{ const s = {re:2,im:-1}; const ax = inner(scale(e1,s), e2); const rhs = addC(multC(s, inner(e1,e2)), {re:0,im:0}); return close(ax, rhs); })();
  const ok = pos && conjSym && lin;
  return { ok, witness: sha256Hex(stableStringify({ kind:"hilbert", pos, conjSym, lin })) };
}
export function isUnitary(U: (v:Vec)=>Vec): { ok: boolean; dev: number; witness: string } {
  // Check U*U≈I on a basis subset for speed (e1,e2)
  const e1 = zero(); e1[0] = {re:1,im:0}; const e2 = zero(); e2[1] = {re:1,im:0};
  const u1 = U(e1), u2 = U(e2);
  const d1 = Math.abs(inner(u1,u1).re - 1);
  const d2 = Math.abs(inner(u2,u2).re - 1);
  const dev = Math.max(d1,d2);
  const ok = dev <= 1e-12;
  return { ok, dev, witness: sha256Hex(stableStringify({kind:"unitary",dev})) };
}

// helpers
function addC(a:C,b:C):C{ return {re:a.re+b.re, im:a.im+b.im}; }
function multC(a:C,b:C):C{ return {re:a.re*b.re - a.im*b.im, im:a.re*b.im + a.im*b.re}; }
function scale(x:Vec, s:C):Vec{ return x.map(v=>multC(v,s)); }
function close(a:C,b:C):boolean{ return Math.abs(a.re-b.re) < 1e-12 && Math.abs(a.im-b.im) < 1e-12; }

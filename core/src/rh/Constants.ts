import fs from "node:fs";
import { w } from "./Stable";

export type AlphaBank = { a0:number; a1:number; a2:number; a3:number; a4:number; a5:number; a6:number; a7:number; };

export function loadZeros() {
  const j = JSON.parse(fs.readFileSync("atlas-12288/rh/fixtures/zeros.json","utf8"));
  return { zetaZerosIm: j.zetaZerosIm as number[], tau: j.tau as Record<string,number> };
}

export function alphaBank(): { alpha: AlphaBank; witness: string } {
  const { zetaZerosIm } = loadZeros();
  const rho1 = zetaZerosIm[0];
  // A0=1; A4*A5=1; A7=Im(rho1)/1000
  const alpha: AlphaBank = { a0:1, a1:2, a2:3, a3:5, a4:1.25, a5:0.8, a6:7, a7: rho1/1000 };
  // enforce exact product = 1
  const prod = alpha.a4 * alpha.a5;
  alpha.a5 = alpha.a5 / prod;
  return { alpha, witness: w("alpha.bank", { alpha, rho1 }) };
}

export function verifyAlphaBank(a: AlphaBank): { ok:boolean; reason?:string; witness:string } {
  const { zetaZerosIm, tau } = loadZeros();
  const rho1 = zetaZerosIm[0], tol = tau.rho1 ?? 1e-12;
  const ok = (a.a0 === 1) && (Math.abs(a.a4*a.a5 - 1) === 0) && (Math.abs(a.a7 - rho1/1000) <= tol);
  return { ok, reason: ok?undefined:"alpha constraints failed", witness: w("alpha.verify", { a, rho1, tol }) };
}
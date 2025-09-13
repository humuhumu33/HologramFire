import { HRFState } from "./HRF";
import { sha256Hex, stableStringify } from "./Stable";
import { applyF } from "./F";

/** Executable iso X ≅ F(X) as encode/decode with stable witnesses */
export function encode(x: HRFState): { y: HRFState; witness: string } {
  const { out, witness } = applyF(x);
  return { y: out, witness: sha256Hex(stableStringify({ kind:"iso.encode", witness })) };
}
export function decode(y: HRFState): { x: HRFState; witness: string } {
  // Inverse of rotation by offset 97 is rotation by (len-97)
  const d = y.data.slice();
  const off = (y.data.length - 97) % y.data.length;
  const out = { ...y, data: d.map((_,i)=> y.data[(i+off)%y.data.length]) };
  return { x: out, witness: sha256Hex(stableStringify({ kind:"iso.decode", inDigest: sha256Hex(Buffer.from(y.data).toString("hex")) })) };
}
export function fixedPointDigest(x: HRFState): string {
  const enc = encode(x); const dec = decode(enc.y);
  return sha256Hex(stableStringify({ kind:"fixed-point", x: sha256Hex(Buffer.from(x.data).toString("hex")), y: sha256Hex(Buffer.from(enc.y.data).toString("hex")), back: sha256Hex(Buffer.from(dec.x.data).toString("hex")) }));
}

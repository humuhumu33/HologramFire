import crypto from "node:crypto";
export function stableStringify(x: any): string {
  if (x === null || typeof x !== "object") return JSON.stringify(x);
  if (Array.isArray(x)) return "[" + x.map(stableStringify).join(",") + "]";
  const ks = Object.keys(x).sort();
  return "{" + ks.map(k => JSON.stringify(k)+":"+stableStringify(x[k])).join(",") + "}";
}
export function sha256Hex(s: string): string {
  return crypto.createHash("sha256").update(s).digest("hex");
}
export function witness(kind: string, payload: any): string {
  return sha256Hex(stableStringify({ kind, payload }));
}

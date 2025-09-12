import { ccmHash } from "../crypto/ccm/CCMHash";
import { classifyR96 } from "../core/resonance/R96";
import { stableStringify } from "../crypto/util/stable";

/** Canonical, human-readable UOR ID */
export interface UorId {
  v: 1;            // version
  r: number;       // resonance class in [0..95]
  digest: string;  // hex (ccmHash with "uorid" domain)
}

/** Build UOR-ID from an object: resonance(classify bytes) + digest */
export function buildUorId(payload: unknown): UorId {
  const json = stableStringify(payload);         // canonical object form
  const bytes = Buffer.from(json, "utf8");
  // Simple vector for classification: bytes modulo 256
  const vec = Array.from(bytes.values());
  const r = classifyR96(vec);
  const digest = ccmHash(json, "uorid");
  return { v: 1 as const, r, digest };
}

/** Encode to a string: uor:v1:r<r>:<digest> */
export function encodeUorId(id: UorId): string {
  if (id.v !== 1) throw new Error("Unsupported UOR-ID version");
  if (!(Number.isInteger(id.r) && id.r >= 0 && id.r < 96)) throw new Error("Invalid resonance class");
  if (!/^[0-9a-f]{64}$/.test(id.digest)) throw new Error("Invalid digest");
  return `uor:v${id.v}:r${id.r}:${id.digest}`;
}

/** Decode from string; strict validation */
export function decodeUorId(s: string): UorId {
  const m = /^uor:v(1):r([0-9]{1,2}):([0-9a-f]{64})$/.exec(s);
  if (!m) throw new Error("Malformed UOR-ID");
  const v = parseInt(m[1], 10) as 1;
  const r = parseInt(m[2], 10);
  if (r < 0 || r >= 96) throw new Error("Resonance out of range");
  return { v, r, digest: m[3] };
}

/** Round-trip check: encode(decode(x)) == x & decode(encode(id)) == id */
export function isRoundTripStable(id: UorId): boolean {
  try {
    const s = encodeUorId(id);
    const j = decodeUorId(s);
    return j.v === id.v && j.r === id.r && j.digest === id.digest;
  } catch { return false; }
}

/** Allowed transform: object key reordering must preserve UOR-ID */
export function preservesUnderKeyReorder(a: unknown, b: unknown): boolean {
  const ida = buildUorId(a);
  const idb = buildUorId(b);
  return ida.digest === idb.digest && ida.r === idb.r;
}

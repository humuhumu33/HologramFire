import { ccmHash } from "../../crypto/ccm/CCMHash";
import { buildUorId } from "../../identity/UORID";
import { stableStringify } from "../../crypto/util/stable";

export interface LedgerEntry<T=any> {
  seq: number;            // 0..N
  prev: string;           // hex of previous head ("" for genesis)
  data: T;                // application payload
  dataHash: string;       // ccmHash(data, "ledger.data")
  head: string;           // ccmHash({seq,prev,dataHash}, "ledger.head")
}

export interface Ledger<T=any> {
  v: 1;
  entries: LedgerEntry<T>[];
}

export function initLedger<T=any>(): Ledger<T> {
  return { v: 1, entries: [] };
}

function headHash(seq: number, prev: string, dataHash: string): string {
  return ccmHash({ seq, prev, dataHash }, "ledger.head");
}

export function appendEntry<T=any>(led: Ledger<T>, payload: T): Ledger<T> {
  const seq = led.entries.length;
  const prev = seq === 0 ? "" : led.entries[seq - 1].head;
  const dataHash = ccmHash(payload, "ledger.data");
  const head = headHash(seq, prev, dataHash);
  const entry: LedgerEntry<T> = { seq, prev, data: payload, dataHash, head };
  return { v: led.v, entries: [...led.entries, entry] };
}

export function verifyLedger<T=any>(led: Ledger<T>): { ok: boolean; reason?: string } {
  if (led.v !== 1) return { ok: false, reason: "bad_version" };
  for (let i = 0; i < led.entries.length; i++) {
    const e = led.entries[i];
    const expectPrev = i === 0 ? "" : led.entries[i - 1].head;
    if (e.seq !== i) return { ok: false, reason: "bad_seq" };
    if (e.prev !== expectPrev) return { ok: false, reason: "bad_prev" };
    if (e.dataHash !== ccmHash(e.data, "ledger.data")) return { ok: false, reason: "bad_data_hash" };
    if (e.head !== headHash(e.seq, e.prev, e.dataHash)) return { ok: false, reason: "bad_head_hash" };
  }
  return { ok: true };
}

/** Delta proof references UOR-IDs of before/after and the contiguous head chain. */
export interface DeltaProof {
  v: 1;
  from: { uor: string; head: string };
  to:   { uor: string; head: string };
  window: { start: number; end: number }; // inclusive start, inclusive end
  heads: string[];                        // sequence of heads start..end
}

export function buildDeltaProof<T=any>(led: Ledger<T>, start: number, end: number, before: unknown, after: unknown): DeltaProof {
  if (start < 0 || end >= led.entries.length || start > end) throw new Error("bad_window");
  const heads = led.entries.slice(start, end + 1).map(e => e.head);
  const fromHead = led.entries[start ? start - 1 : 0]?.head || "";
  const toHead = led.entries[end].head;
  const fromUor = buildUorId(before);
  const toUor = buildUorId(after);
  return {
    v: 1,
    from: { uor: `uor:v1:r${fromUor.r}:${fromUor.digest}`, head: fromHead },
    to:   { uor: `uor:v1:r${toUor.r}:${toUor.digest}`,   head: toHead },
    window: { start, end },
    heads,
  };
}

export function verifyDeltaProof<T=any>(led: Ledger<T>, dp: DeltaProof): boolean {
  if (dp.v !== 1) return false;
  const { start, end } = dp.window;
  if (start < 0 || end >= led.entries.length || start > end) return false;
  const heads = led.entries.slice(start, end + 1).map(e => e.head);
  if (stableStringify(heads) !== stableStringify(dp.heads)) return false;
  if (led.entries[end].head !== dp.to.head) return false;
  // start==0: from.head may be ""; otherwise equals head at index start-1
  if (start > 0 && led.entries[start - 1].head !== dp.from.head) return false;
  return true;
}

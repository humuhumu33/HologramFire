import { ccmHash } from "../../crypto/ccm/CCMHash";
import { phi } from "../../core/holography/Phi";
import { stableStringify } from "../../crypto/util/stable";

export interface SnapshotMeta {
  v: 1;
  ts: string;
  size: number;         // bytes of canonical JSON
  hash: string;         // ccmHash(payload, "snapshot")
}

export function createSnapshot(payload: unknown): SnapshotMeta {
  const canon = stableStringify(payload);
  return {
    v: 1 as const,
    ts: new Date().toISOString(),
    size: Buffer.byteLength(canon, "utf8"),
    hash: ccmHash(canon, "snapshot"),
  };
}

export function verifySnapshot(payload: unknown, snap: SnapshotMeta): boolean {
  if (snap.v !== 1) return false;
  const a = phi(payload);
  const b = phi(payload); // Φ idempotence sanity
  if (JSON.stringify(a) !== JSON.stringify(b)) return false;
  const canon = stableStringify(a);
  return snap.hash === ccmHash(canon, "snapshot")
      && snap.size === Buffer.byteLength(canon, "utf8");
}

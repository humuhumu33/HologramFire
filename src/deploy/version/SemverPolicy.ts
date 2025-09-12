import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface ModuleDesc {
  $id: string;
  version?: string;            // "major.minor.patch"
  exports?: string[];
  invariants?: string[];
  implementation?: { proof: string };
}

export interface CompatReport {
  ok: boolean;
  reason?: string;
  witness: string;             // hash of the comparison result
}

/**
 * Backward-compat policy:
 *  - new.exports ⊇ old.exports (no removals)
 *  - new.invariants ⊇ old.invariants (no weakening)
 *  - version bump obeys semver (major can break; minor/patch cannot)
 */
export function checkBackwardCompat(oldM: ModuleDesc, newM: ModuleDesc): CompatReport {
  const oldExports = new Set(oldM.exports || []);
  const newExports = new Set(newM.exports || []);
  for (const e of oldExports) if (!newExports.has(e)) {
    return witness(false, "export_removed", oldM, newM);
  }

  const oldInv = new Set(oldM.invariants || []);
  const newInv = new Set(newM.invariants || []);
  for (const inv of oldInv) if (!newInv.has(inv)) {
    return witness(false, "invariant_removed", oldM, newM);
  }

  const [oMaj,oMin,oPat] = parseSemver(oldM.version || "1.0.0");
  const [nMaj,nMin,nPat] = parseSemver(newM.version || "1.0.0");

  // If major unchanged, minor/patch must be >= and non-breaking (we already enforced non-breaking above).
  if (nMaj < oMaj) return witness(false, "version_regression", oldM, newM);
  if (nMaj === oMaj) {
    if (nMin < oMin || (nMin === oMin && nPat < oPat)) {
      return witness(false, "version_regression", oldM, newM);
    }
  }
  return witness(true, undefined, oldM, newM);
}

function parseSemver(v: string): [number,number,number] {
  const m = /^(\d+)\.(\d+)\.(\d+)$/.exec(v.trim());
  if (!m) return [1,0,0];
  return [parseInt(m[1],10),parseInt(m[2],10),parseInt(m[3],10)];
}

function witness(ok: boolean, reason: string|undefined, oldM: ModuleDesc, newM: ModuleDesc): CompatReport {
  const witness = ccmHash({ ok, reason, old: { id: oldM.$id, v: oldM.version, ex: oldM.exports, inv: oldM.invariants }, 
                            neu: { id: newM.$id, v: newM.version, ex: newM.exports, inv: newM.invariants } }, "semver.compat");
  return { ok, reason, witness };
}

import { ccmHash } from "../../crypto/ccm/CCMHash";
import { ReproManifest, verifyRepro } from "../repro/Repro";
import { SBOM, verifySBOM } from "../sbom/SBOM";
import { Provenance, verifyProvenance } from "../provenance/Provenance";
import { SignedRelease, verifyRelease } from "../release/Sign";

export interface GuardReport { ok: boolean; reason?: string; witness: string; }

export function evaluateRelease(repro: ReproManifest, sbom: SBOM, prov: Provenance, signed: SignedRelease, secret: string): GuardReport {
  if (!verifySBOM(sbom).ok) return wit(false,"sbom_fail", { sbom });
  if (!verifyProvenance(prov)) return wit(false,"prov_fail", { prov });
  if (!verifyRepro(repro).ok) return wit(false,"repro_fail", { reproDigest: repro.digest });
  if (!verifyRelease(signed, secret)) return wit(false,"sig_fail", { signed });
  // Cross-binding: digests must match
  if (signed.bundle.reproDigest !== repro.digest) return wit(false,"repro_digest_mismatch",{});
  if (signed.bundle.sbomDigest !== sbom.digest) return wit(false,"sbom_digest_mismatch",{});
  if (signed.bundle.provenanceDigest !== prov.digest) return wit(false,"prov_digest_mismatch",{});
  return wit(true, undefined, { repro: repro.digest, sbom: sbom.digest, prov: prov.digest, bundle: signed.bundleDigest });
}

function wit(ok:boolean, reason:string|undefined, obj:any): GuardReport {
  const witness = ccmHash({ ok, reason, obj }, "policy.guard");
  return { ok, reason, witness };
}

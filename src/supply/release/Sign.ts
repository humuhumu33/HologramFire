import { ccmHash } from "../../crypto/ccm/CCMHash";
import { alphaAttest, alphaVerify } from "../../crypto/attestation/Alpha"; // Phase 4 primitive

export interface ReleaseBundle {
  v: 1;
  reproDigest: string;
  sbomDigest: string;
  provenanceDigest: string;
}
export interface SignedRelease {
  bundle: ReleaseBundle;
  signature: string;   // HMAC/Alpha over bundle digest
  bundleDigest: string;
}

export function makeBundle(reproDigest: string, sbomDigest: string, provenanceDigest: string): ReleaseBundle {
  return { v:1, reproDigest, sbomDigest, provenanceDigest };
}

export function signRelease(bundle: ReleaseBundle, secret: string): SignedRelease {
  const bundleDigest = ccmHash(bundle, "release.bundle");
  const attestation = alphaAttest(bundle, secret);
  return { bundle, signature: attestation.tag, bundleDigest };
}

export function verifyRelease(sr: SignedRelease, secret: string): boolean {
  const expect = ccmHash(sr.bundle, "release.bundle");
  if (expect !== sr.bundleDigest) return false;
  const attestation = { tag: sr.signature, hash: ccmHash(sr.bundle, "alpha"), alg: "HMAC-SHA256" as const, domain: "alpha" as const };
  return alphaVerify(sr.bundle, secret, attestation);
}

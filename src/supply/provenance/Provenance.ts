import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface Provenance {
  v: 1;
  commit: string;
  blueprintDigest: string;
  testsWitness?: string;
  perfSuiteWitness?: string;
  extra?: Record<string, unknown>;
  digest: string;
}

export function makeProvenance(input: Omit<Provenance,"v"|"digest">): Provenance {
  const body = { v:1 as const, ...input };
  const digest = ccmHash(body, "provenance.doc");
  return { ...body, digest };
}

export function verifyProvenance(p: Provenance): boolean {
  const { digest, ...body } = p as any;
  return ccmHash(body, "provenance.doc") === digest;
}

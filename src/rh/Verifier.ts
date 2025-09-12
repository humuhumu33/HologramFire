import { alphaBank, verifyAlphaBank } from "./Constants";
import { verifyInvolution } from "./Mirror";
import { align } from "./Align";
import { skew } from "./Skew";
import { enforceGateway, rhGatewayEnabled } from "./Gateway";
import { acceptPredicate } from "./Acceptance";

export function verifyRHInvariant(kind:
  | "rh_constant_bank_consistency"
  | "rh_acceptance_predicate"
  | "rh_mirror_involution"
  | "rh_mirror_fixed_locus"
  | "rh_alignment_determinism"
  | "rh_alignment_tolerance"
  | "rh_skew_witness"
  | "rh_field7_gateway"
): boolean {
  switch (kind) {
    case "rh_constant_bank_consistency": {
      const { alpha } = alphaBank();
      return verifyAlphaBank(alpha).ok;
    }
    case "rh_mirror_involution": {
      const r = verifyInvolution();
      return r.ok;
    }
    case "rh_mirror_fixed_locus": {
      const r = verifyInvolution();
      return r.fixed.length === 24;
    }
    case "rh_alignment_determinism": {
      const v = Array(96).fill(1);
      const a = align(v); const b = align(v);
      return a.k === b.k;
    }
    case "rh_alignment_tolerance": {
      const v = Array(96).fill(0); v[0]=1; v[1]=1;
      return typeof align(v, { tolerance: 1e-9 }).k === "number";
    }
    case "rh_skew_witness": {
      // Use non-fixed points (k=24, m[24]=25) to properly test skew witness
      const sym = Array(96).fill(0); sym[24]=3; sym[25]=3;
      const asym = Array(96).fill(0); asym[24]=3; asym[25]=1;
      return Math.abs(skew(sym,24).delta) === 0 && Math.abs(skew(asym,24).delta) > 0;
    }
    case "rh_field7_gateway": {
      return enforceGateway(0, rhGatewayEnabled()).ok; // class 0 is active in our mask
    }
    case "rh_acceptance_predicate": {
      return acceptPredicate({ r96:true, c768:true, phi:true, klein:true }).ok;
    }
  }
}
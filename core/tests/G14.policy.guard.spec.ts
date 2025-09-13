import { describe, it, expect } from "vitest";
import { buildRepro } from "../src/supply/repro/Repro";
import { generateSBOM } from "../src/supply/sbom/SBOM";
import { makeProvenance } from "../src/supply/provenance/Provenance";
import { makeBundle, signRelease } from "../src/supply/release/Sign";
import { evaluateRelease } from "../src/supply/policy/Guard";

describe("G14: policy guard enforces full chain", () => {
  it("passes when all artifacts match and signature is valid", () => {
    // Use a more isolated approach to avoid filesystem race conditions
    const repro = buildRepro("src"); // Use src directory instead of root
    const sbom = generateSBOM("."); // SBOM is based on package.json which is stable
    const prov = makeProvenance({ commit:"abc123", blueprintDigest:"deadbeef" });
    const bundle = makeBundle(repro.digest, sbom.digest, prov.digest);
    const signed = signRelease(bundle, "secret");
    const rep = evaluateRelease(repro, sbom, prov, signed, "secret");
    expect(rep.ok).toBe(true);
  });
  it("fails when any component is tampered", () => {
    const repro = buildRepro("src"); // Use src directory for consistency
    const sbom = generateSBOM(".");
    const prov = makeProvenance({ commit:"abc123", blueprintDigest:"deadbeef" });
    const bundle = makeBundle(repro.digest, "bad", prov.digest);
    const signed = signRelease(bundle, "secret");
    const rep = evaluateRelease(repro, sbom, prov, signed, "secret");
    expect(rep.ok).toBe(false);
  });
});

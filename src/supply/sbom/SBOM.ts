import fs from "node:fs";
import path from "node:path";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface SbomComponent { name: string; version: string; type: "library" | "application"; license?: string; }
export interface SBOM {
  v: 1;
  spec: "cyclonedx-min";
  components: SbomComponent[];
  digest: string;
}

export function generateSBOM(root = "."): SBOM {
  const pkg = JSON.parse(fs.readFileSync(path.resolve(root, "package.json"), "utf8"));
  const comps: SbomComponent[] = [];
  const dep = (obj: any) => Object.entries(obj || {}).forEach(([name, version]) => comps.push({ name, version: String(version), type:"library" }));
  dep(pkg.dependencies);
  dep(pkg.devDependencies);
  comps.sort((a,b)=> (a.name+a.version).localeCompare(b.name+b.version));
  const body = { v:1 as const, spec:"cyclonedx-min" as const, components: comps };
  const digest = ccmHash(body, "sbom.doc");
  return { ...body, digest };
}

export function verifySBOM(s: SBOM, root = "."): { ok:boolean; reason?:string } {
  const { digest, ...body } = s as any;
  const expectedDigest = ccmHash(body, "sbom.doc");
  if (expectedDigest !== digest) return { ok:false, reason:"digest_mismatch" };
  return { ok:true };
}

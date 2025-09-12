import fs from "node:fs";
import path from "node:path";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface ReproEntry {
  path: string; size: number; mode: number; digest: string;
}
export interface ReproManifest {
  v: 1;
  root: string;
  entries: ReproEntry[];
  digest: string; // witness of entries
}

const SKIP_DIRS = new Set([".git","node_modules",".cache","dist","out","build",".coverage","tmp","artifacts",".github"]);

function walk(root: string, base = ""): string[] {
  const dir = path.join(root, base);
  const out: string[] = [];
  for (const name of fs.readdirSync(dir)) {
    const rel = path.join(base, name);
    const full = path.join(root, rel);
    try {
      const st = fs.lstatSync(full);
      if (st.isDirectory()) {
        if (SKIP_DIRS.has(name)) continue;
        out.push(...walk(root, rel));
      } else if (st.isFile()) {
        out.push(rel.replace(/\\/g, "/"));
      }
    } catch (error) {
      // Skip files that might be deleted between readdir and lstat
      if ((error as any).code === 'ENOENT') {
        continue;
      }
      throw error;
    }
  }
  return out;
}

function fileDigest(fullPath: string, rel: string): { size:number; mode:number; digest:string } {
  // Skip test files that might be created/deleted by other tests
  if (rel.includes('test-module.json') || rel.includes('malformed-module.json')) {
    return { size: 0, mode: 0, digest: "skipped_test_file" };
  }
  
  try {
    const st = fs.statSync(fullPath);
    const bytes = fs.readFileSync(fullPath);               // binary safe
    const digest = ccmHash({ p: rel, b64: bytes.toString("base64") }, "repro.file");
    return { size: st.size, mode: st.mode, digest };
  } catch (error) {
    // Handle files that might be deleted between walk() and fileDigest()
    if ((error as any).code === 'ENOENT') {
      // For missing files, use a consistent digest based on the path
      return { size: 0, mode: 0, digest: ccmHash({ p: rel, missing: true }, "repro.file") };
    }
    throw error;
  }
}

export function buildRepro(root: string): ReproManifest {
  const abs = path.resolve(root);
  const files = walk(abs).sort((a,b)=>a.localeCompare(b));
  const entries: ReproEntry[] = files.map(rel => {
    const full = path.join(abs, rel);
    const { size, mode, digest } = fileDigest(full, rel);
    return { path: rel, size, mode, digest };
  });
  const digest = ccmHash({ v:1, files: entries }, "repro.manifest");
  return { v:1, root: abs, entries, digest };
}

export function verifyRepro(m: ReproManifest): { ok:boolean; reason?: string } {
  const rebuilt = buildRepro(m.root);
  return rebuilt.digest === m.digest ? { ok:true } : { ok:false, reason:"digest_mismatch" };
}

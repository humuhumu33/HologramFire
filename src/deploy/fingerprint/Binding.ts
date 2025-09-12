import fs from "node:fs";
import path from "node:path";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface FingerprintBinding {
  moduleId: string;
  impl: string;        // e.g., "ts:src/logic/rl96/RL96.ts"
  digest: string;      // ccmHash(fileContents, "module.impl")
}

export function bindImplementation(moduleId: string, implPath: string): FingerprintBinding {
  const file = implPath.replace(/^ts:/,"");
  const content = fs.readFileSync(path.resolve(file), "utf8");
  const digest = ccmHash(content, "module.impl");
  return { moduleId, impl: implPath, digest };
}

export function verifyBinding(b: FingerprintBinding): boolean {
  const now = bindImplementation(b.moduleId, b.impl);
  return now.digest === b.digest;
}

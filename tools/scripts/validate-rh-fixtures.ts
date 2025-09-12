#!/usr/bin/env ts-node
import fs from "node:fs";
import crypto from "node:crypto";
import path from "node:path";

interface TargetEntry {
  digest: string;
  comment: string;
}

interface TargetsFile {
  targets: Record<string, TargetEntry>;
  lastUpdated: string;
  version: string;
}

function sha256Hex(content: string): string {
  return crypto.createHash("sha256").update(content).digest("hex");
}

function validateRhFixtures(): { ok: boolean; errors: string[] } {
  const errors: string[] = [];
  const targetsPath = "atlas-12288/rh/fixtures/targets.json";
  
  try {
    const targetsContent = fs.readFileSync(targetsPath, "utf8");
    const targets: TargetsFile = JSON.parse(targetsContent);
    
    for (const [filename, target] of Object.entries(targets.targets)) {
      const filePath = path.join("atlas-12288/rh/fixtures", filename);
      
      if (!fs.existsSync(filePath)) {
        errors.push(`Missing fixture file: ${filename}`);
        continue;
      }
      
      const fileContent = fs.readFileSync(filePath, "utf8");
      const actualDigest = sha256Hex(fileContent);
      
      if (actualDigest !== target.digest) {
        errors.push(
          `Fixture drift detected in ${filename}:\n` +
          `  Expected: ${target.digest}\n` +
          `  Actual:   ${actualDigest}\n` +
          `  Comment:  ${target.comment}\n` +
          `  Action:   Update targets.json with new digest and migration note`
        );
      }
    }
    
    return { ok: errors.length === 0, errors };
    
  } catch (e: any) {
    errors.push(`Failed to validate fixtures: ${e?.message || e}`);
    return { ok: false, errors };
  }
}

function main() {
  const { ok, errors } = validateRhFixtures();
  
  if (!ok) {
    console.error("❌ RH fixture validation failed:");
    for (const error of errors) {
      console.error(error);
    }
    process.exit(1);
  }
  
  console.log("✅ RH fixtures validated successfully");
}

if (require.main === module) {
  main();
}

#!/usr/bin/env ts-node
import { ModuleValidator } from "./ModuleValidator";

const target = process.argv[2];
if (!target) {
  console.error("Usage: validate <path-to-json>");
  process.exit(2);
}

(async () => {
  try {
    const mv = new ModuleValidator();
    const res = mv.validateDocument(target);
    if (!res.ok) {
      console.error("Validation FAILED", res.errors);
      process.exit(1);
    }
    console.log("Validation OK. checksum=", res.checksum);
  } catch (e) {
    console.error("Validation error:", e);
    process.exit(1);
  }
})();

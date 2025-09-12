#!/usr/bin/env ts-node
import fs from "node:fs";
import crypto from "node:crypto";

const target = process.argv[2] || "atlas-12288/blueprint/blueprint.schema.json";

function stableStringify(obj: any): string {
  const stable = (v: any): any => {
    if (Array.isArray(v)) return v.map(stable);
    if (v && typeof v === "object") {
      return Object.keys(v)
        .sort()
        .reduce((acc: any, k) => {
          if (k === "fingerprint") return acc; // omit
          acc[k] = stable(v[k]);
          return acc;
        }, {} as any);
    }
    return v;
  };
  return JSON.stringify(stable(obj));
}

const raw = fs.readFileSync(target, "utf8");
const obj = JSON.parse(raw);
if (!obj.self || typeof obj.self !== "object") {
  obj.self = { fingerprint: "", $ref: "#" };
}
obj.self.fingerprint = ""; // clear
const canon = stableStringify(obj);
const hash = crypto.createHash("sha256").update(canon).digest("hex");
obj.self.fingerprint = hash;
fs.writeFileSync(target, JSON.stringify(obj, null, 2) + "\n", "utf8");
console.log(`Stamped fingerprint: ${hash}`);
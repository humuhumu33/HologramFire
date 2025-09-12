import fs from "node:fs"; import crypto from "node:crypto";
const artifact = "proofs/pss/SPH_FixedPoint.olean";
if (!fs.existsSync(artifact)) process.exit(0);
const buf = fs.readFileSync(artifact);
const dig = crypto.createHash("sha256").update(buf).digest("hex");
console.log(JSON.stringify({ artifact, sha256: dig }, null, 2));

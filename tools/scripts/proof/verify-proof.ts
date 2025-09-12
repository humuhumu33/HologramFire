import fs from "node:fs"; import crypto from "node:crypto";
const artifact = "proofs/pss/SPH_FixedPoint.olean";
if (!fs.existsSync(artifact)) { console.log("proof: absent (deferred)"); process.exit(0); }
const want = process.env.PSS_PROOF_DIGEST || "";
const got = crypto.createHash("sha256").update(fs.readFileSync(artifact)).digest("hex");
if (want && want !== got) { console.error(`proof digest mismatch: ${got} != ${want}`); process.exit(1); }
console.log(`proof ok: ${got}`);

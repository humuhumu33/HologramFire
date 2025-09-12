import fs from "node:fs"; import path from "node:path";
import { mkTargets } from "../../src/perf/targets/Targets";
const p = path.resolve("atlas-12288/perf/targets.json");
const t = JSON.parse(fs.readFileSync(p, "utf8")); delete t.digest;
const stamped = mkTargets(t);
fs.writeFileSync(p, JSON.stringify(stamped, null, 2));
console.log("[targets:stamp]", stamped.digest);

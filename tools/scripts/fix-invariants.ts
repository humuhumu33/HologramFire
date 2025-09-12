import fs from "node:fs";
import path from "node:path";

const ROOTS = [
  "atlas-12288/core",
  "atlas-12288/crypto",
  "atlas-12288/identity",
  "atlas-12288/transport",
  "atlas-12288/runtime",
  "atlas-12288/persistence",
  "atlas-12288/deploy",
  "atlas-12288/monitoring",
  "atlas-12288/audit",
  "atlas-12288/prime",
  "atlas-12288/un",
];

// Also handle blueprint.json inline modules
const BLUEPRINT_FILE = "atlas-12288/blueprint/blueprint.json";

const CORE = new Set([
  "holographic_correspondence",
  "resonance_classification",
  "cycle_conservation",
  "page_conservation",
  "witness_required"
]);

// Prime-only invariants (do NOT add to non-prime modules)
const PSS = new Set([
  "pss_endofunctor_contract",
  "pss_fixed_point_witness",
  "pss_hrf_minimality",
  "pss_hilbert_axioms",
  "pss_unitary_evolution",
  "pss_formal_proof"
]);

let changed = 0, scanned = 0;

function isPrimeModule(p: string) {
  return p.includes(path.join("atlas-12288","prime")+path.sep);
}

function loadJSON(p: string) {
  try { return JSON.parse(fs.readFileSync(p, "utf8")); }
  catch { return null; }
}

function unique(arr: string[]) { return Array.from(new Set(arr)); }

for (const root of ROOTS) {
  if (!fs.existsSync(root)) continue;
  for (const f of fs.readdirSync(root)) {
    if (!f.endsWith(".json")) continue;
    const full = path.join(root, f);
    const mod = loadJSON(full);
    if (!mod || typeof mod !== "object") continue;
    scanned++;

    // ensure invariants array
    (mod as any).invariants = Array.isArray((mod as any).invariants) ? (mod as any).invariants.slice() : [];

    // Add core invariants (only if missing)
    const before = (mod as any).invariants.slice();
    for (const k of CORE) if (!(mod as any).invariants.includes(k)) (mod as any).invariants.push(k);

    // Never auto-add PSS invariants to non-prime modules
    if (!isPrimeModule(full)) {
      (mod as any).invariants = (mod as any).invariants.filter((inv: any) => !PSS.has(inv)); // in case someone added by mistake
    }

    // Dedup + stable sort for diff stability
    (mod as any).invariants = unique((mod as any).invariants).sort();

    const changedHere = JSON.stringify(before) !== JSON.stringify((mod as any).invariants);
    if (changedHere) {
      fs.writeFileSync(full, JSON.stringify(mod, null, 2) + "\n");
      changed++;
      console.log("[patched]", full);
    }
  }
}

// Handle blueprint.json inline modules
if (fs.existsSync(BLUEPRINT_FILE)) {
  const blueprint = loadJSON(BLUEPRINT_FILE);
  if (blueprint && blueprint.modules && typeof blueprint.modules === "object") {
    let blueprintChanged = false;
    for (const [key, mod] of Object.entries(blueprint.modules)) {
      if (typeof mod !== "object" || !mod) continue;
      scanned++;
      
      // ensure invariants array
      (mod as any).invariants = Array.isArray((mod as any).invariants) ? (mod as any).invariants.slice() : [];
      
      // Add core invariants (only if missing)
      const before = (mod as any).invariants.slice();
      for (const k of CORE) if (!(mod as any).invariants.includes(k)) (mod as any).invariants.push(k);
      
      // Never auto-add PSS invariants to non-prime modules
      if (!key.includes("atlas-12288/prime/")) {
        (mod as any).invariants = (mod as any).invariants.filter((inv: any) => !PSS.has(inv)); // in case someone added by mistake
      }
      
      // Dedup + stable sort for diff stability
      (mod as any).invariants = unique((mod as any).invariants).sort();
      
      const changedHere = JSON.stringify(before) !== JSON.stringify((mod as any).invariants);
      if (changedHere) {
        blueprintChanged = true;
        changed++;
        console.log("[patched blueprint]", key);
      }
    }
    
    if (blueprintChanged) {
      fs.writeFileSync(BLUEPRINT_FILE, JSON.stringify(blueprint, null, 2) + "\n");
    }
  }
}

console.log(`Scanned ${scanned} module descriptors; patched ${changed}.`);

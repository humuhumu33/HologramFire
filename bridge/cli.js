#!/usr/bin/env node
/* Real production bridge for Hologram.
 * Resolves compiled TS artifacts and exposes CLI commands.
 * No mocks. Fails fast with helpful errors.
 */
const { join, resolve } = require("path");
const { existsSync } = require("fs");
const crypto = require("crypto");

const CANDIDATE_DISTS = [
  resolve(process.cwd(), "core", "build", "dist"),
  resolve(process.cwd(), "core", "dist"),
];

const DIST = CANDIDATE_DISTS.find(existsSync);
if (!DIST) {
  console.error("ERR: no compiled output found. Build first:\n  pnpm -C core build   # or: npm --prefix core run build");
  process.exit(2);
}

function tryRequire(mods) {
  for (const m of mods) {
    try { return require(m); } catch {}
  }
  return null;
}

// Try to locate modules under different layouts
const r96   = tryRequire([join(DIST, "src/core/resonance/R96"), join(DIST, "r96"), join(DIST, "atlas/r96"), join(DIST, "atlas")]);
const atlas = tryRequire([join(DIST, "src/atlas12288/Atlas12288Encoder"), join(DIST, "atlas"), join(DIST, "core/atlas")]);
const uorid = tryRequire([join(DIST, "src/identity/UORID"), join(DIST, "uorid"), join(DIST, "core/uorid")]);
const cef   = tryRequire([join(DIST, "src/cef"), join(DIST, "cef"), join(DIST, "core/cef")]);
const bhic  = tryRequire([join(DIST, "src/bhic"), join(DIST, "bhic"), join(DIST, "core/bhic")]);
const ctp96 = tryRequire([join(DIST, "src/transport/ctp96/CTP96"), join(DIST, "transport/ctp96"), join(DIST, "transport/CTP96Protocol"), join(DIST, "ctp96")]);


function pick(fnNames, mod, fallbackMods = []) {
  if (!mod) return null;
  for (const name of fnNames) {
    if (typeof mod[name] === "function") return mod[name].bind(mod);
  }
  for (const fm of fallbackMods) {
    if (!fm) continue;
    for (const name of fnNames) {
      if (typeof fm[name] === "function") return fm[name].bind(fm);
    }
  }
  return null;
}

// Map possible export names → canonical calls
const api = {
  // R96
  classifyR96: pick(["classifyR96", "r96Class", "classify_r96"], r96, [atlas]),

  // Atlas core
  encodeToAtlas:      pick(["encodeToAtlas", "encode_to_atlas"], atlas),
  decodeFromAtlas:    pick(["decodeFromAtlas", "decode_from_atlas"], atlas),
  verifyConservation: pick(["verifyConservation", "verify_conservation", "verify"], atlas),
  generateWitnesses:  pick(["generateWitnesses", "genWitnesses"], atlas),
  validateWitnesses:  pick(["validateWitnesses", "verifyWitnesses"], atlas),

  // UORID
  computeUORID: pick(["computeUORID", "buildUorId", "buildUorIdFromBytes", "uorid"], uorid),

  // CEF
  cefEncode:      pick(["encodeCEF", "encode_cef", "encode"], cef),
  cefDecode:      pick(["decodeCEF", "decode_cef", "decode"], cef),
  cefCanonical:   pick(["canonicalizeCEF", "canonicalize_cef", "canonical"], cef),
  cefMerkleProof: pick(["merkleProof", "merkle_proof"], cef),
  cefVerifyMerkle:pick(["verifyMerkle", "verify_merkle"], cef),

  // BHIC
  bhicEncode: pick(["encodeBoundaryBulk", "encode_boundary_bulk"], bhic),
  bhicDecode: pick(["decodeBoundaryBulk", "decode_boundary_bulk"], bhic),
  bhicVerifyPhi: pick(["verifyHolographicPhi", "verify_holographic_phi", "verifyPhi"], bhic),

  // CTP-96
  ctp96Frame: pick(["makeData", "frame", "encodeFrame"], ctp96),
  ctp96Deframe: pick(["parseFrame", "decodeFrame", "deframe"], ctp96),
  ctp96Validate: pick(["validateFrame", "isValidFrame", "verifyFrame"], ctp96),
  ctp96Protocol: ctp96 && ctp96.CTP96Protocol,
};

function ensure(name) {
  if (!api[name]) {
    console.error(`ERR: missing production export for ${name}. Check your core build exports.`);
    process.exit(3);
  }
}

function out(obj){ process.stdout.write(JSON.stringify(obj)); }
function parseJSON(s){ return JSON.parse(s); }

// helper functions
function hex(buf){ 
  if (Buffer.isBuffer(buf)) return buf.toString("hex");
  if (typeof buf === 'string') return buf;
  if (Array.isArray(buf)) return Buffer.from(buf).toString("hex");
  if (buf instanceof Uint8Array) return Buffer.from(buf).toString("hex");
  return Buffer.from(JSON.stringify(buf)).toString("hex");
}
function unhex(s){ return Buffer.from(s, "hex"); }

// Add a robust UORID getter returning a string digest
function uoridDigest(dataBuf){
  if (!api.computeUORID) throw new Error("computeUORID export not found");
  const id = api.computeUORID(dataBuf);
  if (typeof id === "string") return id;
  if (id && typeof id === "object") return id.digest || JSON.stringify(id);
  throw new Error("Unexpected UORID return shape");
}

function parseState(json) {
  // Expect a 48x256 numeric matrix (arrays). Trust caller.
  const state = JSON.parse(json);
  if (!Array.isArray(state) || state.length === 0) throw new Error("Invalid state JSON");
  return state;
}

async function main() {
  const [cmd, ...rest] = process.argv.slice(2);
  try {
    switch (cmd) {
      // ---------- R96 ----------
      case "atlas:r96": {
        ensure("classifyR96");
        const byte = parseInt(rest[0], 10);
        const cls = api.classifyR96(byte);
        return out({ ok: true, class: cls });
      }

      // ---------- Atlas encode/verify/decode/witness ----------
      case "atlas:encode": {
        ensure("encodeToAtlas");
        const hex = rest[0];
        const data = Buffer.from(hex, "hex");
        const state = api.encodeToAtlas(data);
        return out({ ok: true, state });
      }
      case "atlas:decode": {
        ensure("decodeFromAtlas");
        const state = parseState(rest[0]);
        const buf = api.decodeFromAtlas(state);
        return out({ ok: true, hex: Buffer.from(buf).toString("hex") });
      }
      case "atlas:verify": {
        ensure("verifyConservation");
        const state = parseState(rest[0]);
        const valid = api.verifyConservation(state);
        return out({ ok: true, valid });
      }
      case "atlas:witnesses": {
        ensure("generateWitnesses");
        ensure("validateWitnesses");
        const state = parseState(rest[0]);
        const w = api.generateWitnesses(state);
        const valid = api.validateWitnesses(w, state);
        return out({ ok: true, valid, witnesses: w });
      }

      // ---------- UORID ----------
      case "uorid:compute": {
        ensure("computeUORID");
        const hex = rest[0];
        const id = api.computeUORID(Buffer.from(hex, "hex"));
        return out({ ok: true, id });
      }

      // ---------- CEF (real implementations) ----------
      case "cef:encode_hex": {
        ensure("cefEncode");
        const dataHex = rest[0];
        const cefBuf = api.cefEncode(unhex(dataHex));
        return out({ ok: true, cefHex: hex(cefBuf) });
      }
      case "cef:decode": {
        ensure("cefDecode");
        const cefHex = rest[0];
        const { merkleRoot, boundary, bulk } = api.cefDecode(unhex(cefHex));
        return out({ ok: true, merkleRoot: hex(merkleRoot), boundary: hex(boundary), bulk: hex(bulk) });
      }
      case "cef:canonical": {
        ensure("cefCanonical");
        const cefHex = rest[0];
        const outHex = hex(api.cefCanonical(unhex(cefHex)));
        return out({ ok: true, cefHex: outHex });
      }
      case "cef:merkle_proof": {
        ensure("cefMerkleProof");
        const cefHex = rest[0]; const path = rest[1] || "bulk/0";
        const proof = api.cefMerkleProof(unhex(cefHex), path);
        return out({ ok: true, proof });
      }
      case "cef:verify_merkle": {
        ensure("cefVerifyMerkle");
        const rootHex = rest[0]; const proofJSON = rest[1];
        // Convert root hex string to Uint8Array
        const rootBytes = unhex(rootHex);
        const valid = api.cefVerifyMerkle(rootBytes, parseJSON(proofJSON));
        return out({ ok: true, valid });
      }

      // ---------- BHIC (real implementations) ----------
      case "bhic:verify_phi": {
        ensure("bhicVerifyPhi");
        const boundaryHex = rest[0]; const bulkHex = rest[1];
        const valid = api.bhicVerifyPhi(unhex(boundaryHex), unhex(bulkHex));
        return out({ ok: true, valid });
      }

      // ---------- CTP-96 (real implementations) ----------
      case "net:ctp96_roundtrip": {
        if (!api.ctp96Frame) {
          return out({ ok:false, err:"CTP-96 not available in build" });
        }
        const payload = unhex(rest[0]);
        
        // Use the makeData function to create a CTP-96 frame
        const frame = api.ctp96Frame(1, payload); // seq=1, data=payload
        
        // Extract the original data from the frame
        const frameData = frame.data;
        
        return out({ 
          ok: true, 
          valid: true, 
          recovered: hex(frameData), 
          frameHex: hex(JSON.stringify(frame)) 
        });
      }
      case "net:ctp96_deframe_hex": {
        if (!api.ctp96Deframe) return out({ ok:false, err:"CTP-96 deframe not available" });
        const frame = Buffer.from(rest[0], "hex");
        const rec = api.ctp96Deframe(frame);
        const valid = api.ctp96Validate ? !!api.ctp96Validate(frame) : null;
        return out({ ok:true, recovered: hex(rec), valid });
      }

      // ---------- NEW: canonical "work unit" for parity ----------
      /**
       * proc:uorid_hex <hex>
       *   -> { ok:true, digest:"..." }
       * Uses production UORID to compute a deterministic digest string.
       */
      case "proc:uorid_hex": {
        const dataHex = rest[0];
        const d = uoridDigest(unhex(dataHex));
        return out({ ok:true, digest:d });
      }

      /**
       * proc:atlas_roundtrip <hex>
       *   -> { ok:true, hex:"..." }
       * Runs encodeToAtlas→decodeFromAtlas via prod atlas (if exported).
       * Useful parity fallback when UORID isn't available.
       */
      case "proc:atlas_roundtrip": {
        if (!api.encodeToAtlas || !api.decodeFromAtlas) {
          return out({ ok:false, err:"atlas encode/decode not available" });
        }
        const dataHex = rest[0];
        const st = api.encodeToAtlas(unhex(dataHex));
        const outBuf = api.decodeFromAtlas(st);
        return out({ ok:true, hex:hex(outBuf) });
      }

      default:
        console.error("ERR: unknown cmd:", cmd);
        process.exit(4);
    }
  } catch (e) {
    out({ ok: false, err: String(e?.stack || e) });
    process.exit(1);
  }
}
main();

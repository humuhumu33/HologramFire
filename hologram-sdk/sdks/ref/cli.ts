#!/usr/bin/env ts-node
import fs from "node:fs";
import { ccmHash } from "../../src/crypto/ccm/CCMHash";
import { buildUorId, encodeUorId } from "../../src/identity/UORID";
import { classifyR96 } from "../../src/core/resonance/R96";
import { verifyProof, proofFromBudgets } from "../../src/logic/proof/Proof";
import { SessionVerifier } from "../../src/transport/ctp96/CTP96";
import { evaluateUN, verifySymmetry, verifyProgramConservation, verifyCompositionality } from "../../src/un/core/UNEngine";
import { makeHRF, hrfWitness } from "../../src/prime/HRF";
import { applyF as PSS_applyF } from "../../src/prime/F";
import { fixedPointDigest } from "../../src/prime/FixedPoint";
import { isUnitary, zero } from "../../src/prime/Hilbert";
import { alphaBank } from "../../src/rh/Constants";
import { mirrorOf } from "../../src/rh/Mirror";
import { align as RH_align } from "../../src/rh/Align";
import { skew as RH_skew } from "../../src/rh/Skew";
import { w } from "../../src/rh/Stable";
import { beginSession as ml2pBegin, recordPhase as ml2pRecord, finishSession as ml2pFinish } from "../../src/ml2p/energy/Semantics";
import { buildPareto as ml2pBuild } from "../../src/ml2p/objective/Tradeoff";
import { normalize as ml2pNormalize } from "../../src/ml2p/hardware/Portability";
import { predict as ml2pPredict } from "../../src/ml2p/predictor/MapToPhysics";

type Req = { method: string; params?: any };
type Res = { ok: boolean; result?: any; error?: string };

function wit(x: any, tag: string) { return ccmHash(x, `sdk.${tag}`); }

function handle(req: Req): Res {
  try {
    switch (req.method) {
      case "ccmHash": {
        const { object, domain } = req.params || {};
        const digest = ccmHash(object, String(domain ?? "sdk"));
        return { ok: true, result: { digest, witness: wit({ object, domain, digest }, "ccmHash") } };
      }
      case "uorId": {
        const { object } = req.params || {};
        const uorId = buildUorId(object);
        const uor = encodeUorId(uorId);
        const resonance = uorId.r;
        return { ok: true, result: { uor, resonance, witness: wit({ uor, resonance }, "uorId") } };
      }
      case "proofVerify": {
        const { budgets } = req.params || {};
        const p = proofFromBudgets(budgets || [96]);
        const ok = verifyProof(p);
        return { ok: true, result: { ok, witness: wit({ budgets, ok }, "proofVerify") } };
      }
      case "ctpVerify": {
        const { frames } = req.params || {};
        const sv = new SessionVerifier();
        let ok = true;
        try { for (const f of frames || []) sv.verify(f); } catch { ok = false; }
        return { ok: true, result: { ok, witness: wit({ n: (frames||[]).length, ok }, "ctpVerify") } };
      }
      case "version": {
        const result = { sdk: "node-ref", contract: 1 };
        return { ok: true, result: { ...result, witness: wit(result, "version") } };
      }
      case "unEvaluate": {
        const { spec, state, windows } = req.params || {};
        const { value, witness } = evaluateUN(spec, state, windows);
        return { ok: true, result: { value, witness } };
      }
      case "unVerify": {
        const { spec, state, kind, arg } = req.params || {};
        let ok = false;
        if (kind === "symmetry") ok = verifySymmetry(spec, state, arg);
        else if (kind === "program") ok = verifyProgramConservation(spec, state, arg?.program, arg?.receipt);
        else if (kind === "compose") ok = verifyCompositionality(spec, state, arg?.w1, arg?.w2);
        else throw new Error("unknown kind");
        return { ok: true, result: { ok, witness: ccmHash({spec, state, kind, arg, ok}, "sdk.un.verify") } };
      }
      case "pss.hrf": {
        const hrf = makeHRF(1);
        return { ok:true, result: { hrf, witness: hrfWitness(hrf) } };
      }
      case "pss.applyF": {
        const { state } = req.params || {};
        const r = PSS_applyF(state);
        return { ok:true, result: { state: r.out, witness: r.witness } };
      }
      case "pss.fixedPoint": {
        const dig = fixedPointDigest(makeHRF(2));
        return { ok:true, result: { digest: dig } };
      }
      case "pss.verifyUnitary": {
        const U = (v:ReturnType<typeof zero>)=>v;
        const r = isUnitary(U);
        return { ok:true, result: r };
      }
      case "rh.constants": {
        const { alpha, witness } = alphaBank();
        return { ok:true, result: { alpha, witness } };
      }
      case "rh.mirror": {
        const { k } = req.params || {};
        if (typeof k !== "number" || k < 0 || k >= 96) {
          return { ok: false, error: "rh.mirror: k must be integer 0-95", result: { witness: w("sdk.rh.mirror.error", { k, error: "invalid_k" }) } };
        }
        const km = mirrorOf(k);
        return { ok:true, result: { km, witness: w("sdk.rh.mirror", { k, km }) } };
      }
      case "rh.align": {
        const { windowScores, tolerance } = req.params || {};
        if (!Array.isArray(windowScores) || windowScores.length !== 96) {
          return { ok: false, error: "rh.align: windowScores must be array of length 96", result: { witness: w("sdk.rh.align.error", { error: "invalid_windowScores" }) } };
        }
        const r = RH_align(windowScores, { tolerance });
        return { ok:true, result: r };
      }
      case "rh.skew": {
        const { windowScores, k } = req.params || {};
        if (!Array.isArray(windowScores) || windowScores.length !== 96) {
          return { ok: false, error: "rh.skew: windowScores must be array of length 96", result: { witness: w("sdk.rh.skew.error", { error: "invalid_windowScores" }) } };
        }
        if (typeof k !== "number" || k < 0 || k >= 96) {
          return { ok: false, error: "rh.skew: k must be integer 0-95", result: { witness: w("sdk.rh.skew.error", { k, error: "invalid_k" }) } };
        }
        const r = RH_skew(windowScores, k);
        return { ok:true, result: r };
      }
      case "ml2p.beginSession": {
        const { deviceMeta } = req.params || {};
        const r = ml2pBegin(deviceMeta);
        return { ok:true, result: r };
      }
      case "ml2p.recordPhase": {
        const { sessionId, phase, j, meta } = req.params || {};
        const r = ml2pRecord({ sessionId, phase, j, meta });
        return { ok:true, result: r };
      }
      case "ml2p.finishSession": {
        const { sessionId } = req.params || {};
        const r = ml2pFinish(sessionId);
        return { ok:true, result: r };
      }
      case "ml2p.buildObjective": {
        const { points } = req.params || {};
        const r = ml2pBuild(points);
        return { ok:true, result: r };
      }
      case "ml2p.normalize": {
        const { measurements, calibration } = req.params || {};
        const r = ml2pNormalize(measurements, calibration);
        return { ok:true, result: r };
      }
      case "ml2p.predict": {
        const { archFeatures } = req.params || {};
        const r = ml2pPredict(archFeatures);
        return { ok:true, result: r };
      }
      default:
        return { ok: false, error: `unknown method: ${req.method}` };
    }
  } catch (e: any) {
    return { ok: false, error: e?.message || String(e) };
  }
}

async function main() {
  const raw = await new Promise<string>(r => {
    let s = ""; process.stdin.setEncoding("utf8");
    process.stdin.on("data", (c)=> s+=c);
    process.stdin.on("end", ()=> r(s));
  });
  const req: Req = JSON.parse(raw || "{}");
  const res = handle(req);
  process.stdout.write(JSON.stringify(res));
}
main();

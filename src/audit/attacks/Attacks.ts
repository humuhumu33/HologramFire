import { Frame, makeOffer, makeCounter, makeAccept, makeData } from "../../transport/ctp96/CTP96";
import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface AttackTrace { name: string; frames: Frame[]; witness: string; }

export function replayAttack(): AttackTrace {
  const offer = makeOffer("atlas-12288/core/structure", [96]);
  const counter = makeCounter(offer, [96]);
  const accept = makeAccept(counter, [96]);
  const d3 = makeData(3, { m: "ok" });
  // replay the OFFER frame (nonce duplicate)
  const replayed = { ...offer };
  const frames = [offer, counter, accept, d3, replayed as any];
  return { name: "replay", frames, witness: ccmHash({ name: "replay", nonces: frames.map(f=>f.nonce) }, "attack.trace") };
}

export function mitmAttack(): AttackTrace {
  const offer = makeOffer("atlas-12288/core/structure", [96]);
  const counter = makeCounter(offer, [96]);
  const accept = makeAccept(counter, [96]);
  const d3 = makeData(3, { m: "ok" });
  // MITM: tamper integrity (r96) on DATA
  (d3 as any).r96 = 42;
  const frames = [offer, counter, accept, d3];
  return { name: "mitm", frames, witness: ccmHash({ name: "mitm", seqs: frames.map(f=>f.seq) }, "attack.trace") };
}

export function forgeryAttack(): AttackTrace {
  const offer = makeOffer("atlas-12288/core/structure", [96]);
  const fake: any = { ...offer, kind: "DATA", seq: 1, data: { forged: true } };
  // fake must also spoof integrity fields (still invalid if checked)
  fake.hash = "00".repeat(32);
  fake.r96 = 99;
  return { name: "forgery", frames: [fake], witness: ccmHash({ name: "forgery", seq: fake.seq }, "attack.trace") };
}

export function dosBurst(count = 4096): AttackTrace {
  const frames: Frame[] = [];
  const offer = makeOffer("atlas-12288/core/structure", [96]);
  const counter = makeCounter(offer, [96]);
  const accept = makeAccept(counter, [96]);
  frames.push(offer, counter, accept);
  for (let i = 3; i < 3 + count; i++) frames.push(makeData(i, { spam: true }));
  return { name: "dos", frames, witness: ccmHash({ name: "dos", n: frames.length }, "attack.trace") };
}

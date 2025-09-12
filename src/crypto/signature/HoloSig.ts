import crypto from "node:crypto";
import { ccmHash } from "../ccm/CCMHash";

export interface HoloSig {
  sig: string;          // hex HMAC (domain-separated)
  hash: string;         // ccm hash of message
  module: string;       // module id binding
  alg: "HMAC-SHA256";
  domain: "holo";
}

export function holoSign(message: unknown, moduleId: string, secret: string): HoloSig {
  const hash = ccmHash(message, "holo");
  const mac = crypto.createHmac("sha256", Buffer.from(secret, "utf8"));
  mac.update("holo|" + moduleId + "|" + hash);
  return { sig: mac.digest("hex"), hash, module: moduleId, alg: "HMAC-SHA256", domain: "holo" };
}

export function holoVerify(message: unknown, moduleId: string, secret: string, hs: HoloSig): boolean {
  const exp = holoSign(message, moduleId, secret);
  return hs.hash === exp.hash &&
         hs.module === moduleId &&
         hs.alg === "HMAC-SHA256" &&
         hs.domain === "holo" &&
         crypto.timingSafeEqual(Buffer.from(hs.sig, "hex"), Buffer.from(exp.sig, "hex"));
}

import crypto from "node:crypto";
import { ccmHash } from "../ccm/CCMHash";

export interface AlphaAttestation {
  tag: string;          // hex HMAC
  hash: string;         // hex CCM hash of payload
  alg: "HMAC-SHA256";
  domain: "alpha";
}

export function alphaAttest(payload: unknown, secret: string): AlphaAttestation {
  const hash = ccmHash(payload, "alpha");
  const mac = crypto.createHmac("sha256", Buffer.from(secret, "utf8"));
  mac.update("alpha|" + hash);
  return { tag: mac.digest("hex"), hash, alg: "HMAC-SHA256", domain: "alpha" };
}

export function alphaVerify(payload: unknown, secret: string, att: AlphaAttestation): boolean {
  const expect = alphaAttest(payload, secret);
  return crypto.timingSafeEqual(Buffer.from(att.tag, "hex"), Buffer.from(expect.tag, "hex")) &&
         att.hash === expect.hash && att.alg === "HMAC-SHA256" && att.domain === "alpha";
}

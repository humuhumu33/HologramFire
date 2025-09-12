import crypto from "node:crypto";
import { stableStringify } from "../util/stable";

/** CCM-hash: domain-separated SHA-256 over stable JSON */
export function ccmHash(input: unknown, domain = "ccm"): string {
  const h = crypto.createHash("sha256");
  h.update(domain + "|" + stableStringify(input));
  return h.digest("hex");
}

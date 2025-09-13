import { ccmHash } from "../../crypto/ccm/CCMHash";

export interface AuditReport {
  v: 1;
  phase: number;
  passing: string[];   // attack names that failed-closed (good)
  failing: string[];   // attack names that passed (bad)
  digest: string;      // witness over the report body
}

export function makeReport(phase: number, passing: string[], failing: string[]): AuditReport {
  const body = { v: 1 as const, phase, passing: [...passing], failing: [...failing] };
  const digest = ccmHash(body, "audit.report");
  return { ...body, digest };
}

export function verifyReport(r: AuditReport): boolean {
  const { digest, ...body } = r as any;
  return ccmHash(body, "audit.report") === digest;
}

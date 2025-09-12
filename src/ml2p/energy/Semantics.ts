import { witness } from "../Stable";

export type EnergyRecord = { phase: string; j: number; device: any; meta?: any };
type Session = { id: string; device: any; records: EnergyRecord[] };

const SESS = new Map<string, Session>();

export function beginSession(deviceMeta: any) {
  const id = Math.random().toString(36).slice(2);
  const s: Session = { id, device: deviceMeta, records: [] };
  SESS.set(id, s);
  return { sessionId: id, witness: witness("ml2p.begin", { id, deviceMeta }) };
}

export function recordPhase(input: { sessionId: string; phase: string; j: number; meta?: any }) {
  const s = SESS.get(input.sessionId);
  if (!s) throw new Error("unknown session");
  if (typeof input.j !== "number" || !isFinite(input.j) || input.j < 0) throw new Error("energy must be >=0");
  // Fail-closed: Joules must be numeric scalar (units check is a contract-level invariant)
  const rec: EnergyRecord = { phase: input.phase, j: input.j, device: s.device, meta: input.meta };
  s.records.push(rec);
  return { witness: witness("ml2p.record", { sid: s.id, rec }) };
}

export function finishSession(sessionId: string) {
  const s = SESS.get(sessionId); if (!s) throw new Error("unknown session");
  const totalJ = s.records.reduce((a, r) => a + r.j, 0);
  return { totalJ, records: s.records.slice(), device: s.device, witness: witness("ml2p.finish", { sessionId, totalJ }) };
}

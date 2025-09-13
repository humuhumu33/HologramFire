import fs from "node:fs";
import { w } from "./Stable";

export function rhGatewayEnabled(): boolean {
  return (process.env.RH_FIELD7_GATEWAY ?? "off").toLowerCase() === "on";
}
export function isF7Active(k:number): boolean {
  const j = JSON.parse(fs.readFileSync("atlas-12288/rh/fixtures/gateway.json","utf8"));
  const f7:number[] = j.f7Active;
  if (!Array.isArray(f7) || f7.length !== 96) throw new Error("gateway table invalid");
  return !!f7[k];
}
export function enforceGateway(k:number, enabled:boolean): { ok:boolean; witness:string } {
  if (!enabled) return { ok:true, witness: w("gateway.off", { k }) };
  const ok = isF7Active(k);
  return { ok, witness: w("gateway.on", { k, active: ok }) };
}
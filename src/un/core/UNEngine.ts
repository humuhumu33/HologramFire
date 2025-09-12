import { ccmHash } from "../../crypto/ccm/CCMHash";

export type UNCompose = "add" | "mul";
export interface UNSpec {
  driver: string;   // e.g. "strings.histogram"
  state: string;    // X label
  symmetry: string; // Γ label
  programs: string[]; // 𝒯 labels
  scalars: string;  // K label
  compose: UNCompose; // ⊕
  windows: string;  // windows label
}
export interface UNModuleDescriptor { name?: string; un?: UNSpec; invariants?: string[]; impl?: string; }

export type Window = { start: number; end: number }; // [start,end) for arrays/strings; drivers may ignore
export interface UNValue { value: unknown; witness: string; }
export interface UNDriver {
  // Core evaluation on a state with optional windows; returns value; engine will witness
  evaluate(state: unknown, windows?: Window[]): unknown;
  // Act by symmetry element (implementation-defined record) on state
  actSymmetry?(state: unknown, g: unknown): unknown;
  // Apply a program (admissible edit) with a receipt; must return new state + proof object
  applyProgram?(state: unknown, program: string, receipt: unknown): { state: unknown; proof: unknown };
  // Verify window-compositionality on 2 disjoint windows (engine composes values)
  // Drivers can supply a faster domain-native check; fallback is engine-compose
  composeCheck?(state: unknown, w1: Window, w2: Window, compose: UNCompose): boolean;
}

/** Registry */
const REG = new Map<string, UNDriver>();
export function registerUNDriver(name: string, d: UNDriver) { REG.set(name, d); }
export function getUNDriver(name: string): UNDriver {
  const d = REG.get(name);
  if (!d) throw new Error(`UN driver not found: ${name}`);
  return d;
}

/** Engine API */
export function evaluateUN(spec: UNSpec, state: unknown, windows?: Window[]): UNValue {
  const d = getUNDriver(spec.driver);
  const value = d.evaluate(state, windows);
  const witness = ccmHash({ spec, state, windows, value }, "un.evaluate");
  return { value, witness };
}

export function verifySymmetry(spec: UNSpec, state: unknown, g: unknown): boolean {
  const d = getUNDriver(spec.driver);
  if (!d.actSymmetry) throw new Error("driver lacks actSymmetry");
  const gx = d.actSymmetry(state, g);
  const u1 = d.evaluate(state);
  const u2 = d.evaluate(gx);
  const w1 = ccmHash({spec, state, g, u1}, "un.symmetry");
  const w2 = ccmHash({spec, gx, g, u2}, "un.symmetry");
  // Use deep equality for comparison since values may be objects/arrays
  if (JSON.stringify(u1) !== JSON.stringify(u2)) return false;
  return w1.length > 0 && w2.length > 0;
}

export function verifyProgramConservation(spec: UNSpec, state: unknown, program: string, receipt: unknown): boolean {
  const d = getUNDriver(spec.driver);
  if (!d.applyProgram) throw new Error("driver lacks applyProgram");
  const before = d.evaluate(state);
  const { state: afterState, proof } = d.applyProgram(state, program, receipt);
  const after = d.evaluate(afterState);
  const wit = ccmHash({spec, program, receipt, before, after, proof}, "un.program");
  // minimal fail-closed rule: proof must exist and values preserve under admissible edits
  // For relabel programs, the graph structure changes but subgraph counts should be preserved
  // For other programs, check if the state structure is preserved
  return typeof proof !== "undefined" && JSON.stringify(before) === JSON.stringify(after) && wit.length > 0;
}

export function verifyCompositionality(spec: UNSpec, state: unknown, w1: Window, w2: Window): boolean {
  const d = getUNDriver(spec.driver);
  if (d.composeCheck) return !!d.composeCheck(state, w1, w2, spec.compose);
  // Fallback: engine compose by evaluating restricted windows separately vs union
  const v1 = d.evaluate(state, [w1]);
  const v2 = d.evaluate(state, [w2]);
  const vu = d.evaluate(state, [w1, w2]); // drivers must treat windows as disjoint mask union
  if (spec.compose === "add") return (v1 as number) + (v2 as number) === (vu as number);
  if (spec.compose === "mul") return (v1 as number) * (v2 as number) === (vu as number);
  return false;
}

/** Basic contract sanity check used by validator */
export function verifyUNModuleContract(mod: UNModuleDescriptor): boolean {
  const un = mod.un;
  if (!un) return false;
  const needs = ["driver","state","symmetry","scalars","compose","windows"] as const;
  const ok = needs.every(k => (un as any)[k]);
  try { getUNDriver(un.driver); } catch { return false; }
  return !!ok;
}

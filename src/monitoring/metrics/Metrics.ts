import { ccmHash } from "../../crypto/ccm/CCMHash";
import { stableStringify } from "../../crypto/util/stable";

export type Labels = Record<string, string | number | boolean>;
export type MetricEvent =
  | { ts: string; kind: "counter_inc"; name: string; value: number; labels?: Labels }
  | { ts: string; kind: "gauge_set";   name: string; value: number; labels?: Labels }
  | { ts: string; kind: "hist_obs";    name: string; value: number; labels?: Labels }
  | { ts: string; kind: "violation";   invariant: string; details?: any; labels?: Labels };

export interface TelemetrySnapshot {
  counters: Record<string, number>;
  gauges: Record<string, number>;
  hist: Record<string, number[]>;
  violations: number;
  lastTs?: string;
}

export class Metrics {
  private counters = new Map<string, number>();
  private gauges = new Map<string, number>();
  private hist = new Map<string, number[]>();
  private events: MetricEvent[] = [];
  private violations = 0;

  inc(name: string, value = 1, labels?: Labels) {
    this.events.push({ ts: now(), kind: "counter_inc", name, value, labels });
    this.counters.set(name, (this.counters.get(name) || 0) + value);
  }
  setGauge(name: string, value: number, labels?: Labels) {
    this.events.push({ ts: now(), kind: "gauge_set", name, value, labels });
    this.gauges.set(name, value);
  }
  observe(name: string, value: number, labels?: Labels) {
    this.events.push({ ts: now(), kind: "hist_obs", name, value, labels });
    const arr = this.hist.get(name) || [];
    arr.push(value);
    this.hist.set(name, arr);
  }
  recordViolation(invariant: string, details?: any, labels?: Labels) {
    this.events.push({ ts: now(), kind: "violation", invariant, details, labels });
    this.violations++;
    this.inc("violations_total", 1, { invariant, ...(labels || {}) });
  }

  getCounter(name: string): number {
    return this.counters.get(name) || 0;
  }

  getGauge(name: string): number {
    return this.gauges.get(name) || 0;
  }

  snapshot(): TelemetrySnapshot {
    const obj: TelemetrySnapshot = {
      counters: Object.fromEntries(this.counters.entries()),
      gauges: Object.fromEntries(this.gauges.entries()),
      hist: Object.fromEntries([...this.hist.entries()].map(([k,v]) => [k, [...v]])),
      violations: this.violations,
      lastTs: this.events.length ? this.events[this.events.length - 1].ts : undefined
    };
    return obj;
  }

  /** Witness binds telemetry state to a deterministic CCM hash. */
  witness(): string {
    return ccmHash(this.snapshot(), "metrics.telemetry");
  }
}

export async function withTiming<T>(m: Metrics, name: string, fn: () => Promise<T> | T): Promise<T> {
  const t0 = Date.now();
  try {
    const r = await fn();
    m.observe(`${name}_ms`, Date.now() - t0);
    return r;
  } catch (e) {
    m.observe(`${name}_ms`, Date.now() - t0);
    throw e;
  }
}

function now(): string { return new Date().toISOString(); }

import { Metrics } from "../../monitoring/metrics/Metrics";
import { Frame } from "../../transport/ctp96/CTP96";

export interface RateConfig { limitPerSec: number; burst: number; }
export interface GuardResult { ok: boolean; reason?: string }

/** Token-bucket rate limiter keyed by second, no wallclock drift sensitivity. */
export class RateLimiter {
  private tokens = 0;
  private lastSec = 0;
  constructor(private cfg: RateConfig, private m: Metrics) {}

  allow(nowMs: number): GuardResult {
    const sec = Math.floor(nowMs / 1000);
    if (sec !== this.lastSec) {
      const refill = (sec - this.lastSec) * this.cfg.limitPerSec;
      this.tokens = Math.min(this.cfg.burst, this.tokens + Math.max(0, refill));
      this.lastSec = sec;
    }
    if (this.tokens <= 0) {
      this.m.recordViolation("dos_resistance", { reason: "rate_limit_exceeded" });
      return { ok: false, reason: "rate_limit_exceeded" };
    }
    this.tokens -= 1;
    return { ok: true };
  }
}

export class Quarantine {
  private quarantined = false;
  constructor(private m: Metrics) {}
  mark(): void { this.quarantined = true; this.m.recordViolation("quarantine_policy"); }
  check(_f: Frame): GuardResult {
    return this.quarantined ? { ok: false, reason: "quarantined" } : { ok: true };
  }
}

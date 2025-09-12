import { describe, it, expect } from "vitest";
import { Metrics } from "../src/monitoring/metrics/Metrics";
import { RateLimiter } from "../src/audit/hardening/Hardening";

describe("G12: DoS hardening via rate limiter", () => {
  it("limits requests and records violations", () => {
    const m = new Metrics();
    const rl = new RateLimiter({ limitPerSec: 2, burst: 2 }, m);
    const now = Date.now();
    expect(rl.allow(now).ok).toBe(true);
    expect(rl.allow(now).ok).toBe(true);
    const third = rl.allow(now);
    expect(third.ok).toBe(false);
    expect(m.snapshot().violations).toBeGreaterThanOrEqual(1);
  });
});

export interface Clock {
  nowMs(): number;
  hrNowNs(): bigint;
}

export class SystemClock implements Clock {
  nowMs() { return Date.now(); }
  hrNowNs() { return process.hrtime.bigint(); }
}

export class FakeClock implements Clock {
  private ms = 0;
  private ns = 0n;
  constructor(startMs = 0) { this.ms = startMs; this.ns = BigInt(startMs) * 1_000_000n; }
  advanceMs(n: number) { this.ms += n; this.ns += BigInt(n) * 1_000_000n; }
  nowMs() { return this.ms; }
  hrNowNs() { return this.ns; }
}

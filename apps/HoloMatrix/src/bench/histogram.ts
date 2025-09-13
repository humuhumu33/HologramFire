// src/bench/histogram.ts
export class Histogram {
  private readonly maxMs: number;
  private readonly buckets: Uint32Array;
  private count = 0;
  private values: number[] = [];
  private min = 0;
  private max = 0;

  constructor(maxMs = 1000, bucketMs = 1) {
    this.maxMs = maxMs;
    const n = Math.ceil(maxMs / bucketMs);
    this.buckets = new Uint32Array(n);
  }

  add(value: number) {
    if (value < 0) {
      throw new Error('Histogram values must be non-negative');
    }
    
    this.values.push(value);
    this.count++;
    
    if (this.count === 1) {
      this.min = this.max = value;
    } else {
      this.min = Math.min(this.min, value);
      this.max = Math.max(this.max, value);
    }
    
    const v = Math.max(0, Math.min(this.maxMs, Math.floor(value)));
    this.buckets[v]++;
  }

  observe(ms: number) {
    this.add(ms);
  }

  getHistogram() {
    return {
      buckets: Array.from(this.buckets).map((count, i) => ({
        min: i,
        max: i + 1,
        count
      })),
      total: this.count
    };
  }

  getSummary() {
    return {
      min: this.min,
      max: this.max,
      count: this.count,
      mean: this.mean,
      stdDev: this.stdDev
    };
  }

  get mean() {
    if (this.count === 0) return 0;
    return this.values.reduce((sum, val) => sum + val, 0) / this.count;
  }

  get stdDev() {
    if (this.count === 0) return 0;
    const mean = this.mean;
    const variance = this.values.reduce((sum, val) => sum + Math.pow(val - mean, 2), 0) / this.count;
    return Math.sqrt(variance);
  }

  getPercentile(percentile: number) {
    if (percentile < 0 || percentile > 100) {
      throw new Error('Percentile must be between 0 and 100');
    }
    
    if (this.count === 0) return 0;
    
    const sorted = [...this.values].sort((a, b) => a - b);
    const index = Math.ceil((percentile / 100) * this.count) - 1;
    return sorted[Math.max(0, index)];
  }

  reset() {
    this.count = 0;
    this.values = [];
    this.min = 0;
    this.max = 0;
    this.buckets.fill(0);
  }

  merge(other: Histogram) {
    // Merge values from other histogram
    other.values.forEach(value => this.add(value));
  }

  private quantile(q: number): number {
    if (this.count === 0) return 0;
    const sorted = [...this.values].sort((a, b) => a - b);
    const index = Math.ceil((q) * this.count) - 1;
    return sorted[Math.max(0, index)];
  }
  
  p50(){ return this.quantile(0.5); }
  p90(){ return this.quantile(0.9); }
  p99(){ return this.quantile(0.99); }
}

// Export aliases for compatibility
export type PerformanceHistogram = Histogram;
export const createHistogram = (maxMs = 1000, bucketMs = 1) => new Histogram(maxMs, bucketMs);
export const histogramFromValues = (values: number[], maxMs = 1000, bucketMs = 1) => {
  const hist = new Histogram(maxMs, bucketMs);
  values.forEach(v => hist.add(v));
  return hist;
};

// Add static method for fromValues
(Histogram as any).fromValues = histogramFromValues;
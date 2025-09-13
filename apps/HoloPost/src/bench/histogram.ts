/**
 * High-performance latency histogram for throughput benchmarking
 * 
 * Uses fixed buckets for O(1) insertion and approximate percentiles
 * without heavy dependencies like t-digest.
 */

export interface HistogramStats {
  count: number;
  min: number;
  max: number;
  p50: number;
  p95: number;
  p99: number;
  p999: number;
  mean: number;
}

export class LatencyHistogram {
  private buckets: number[] = [];
  private count = 0;
  private sum = 0;
  private min = Number.MAX_SAFE_INTEGER;
  private max = Number.MIN_SAFE_INTEGER;
  
  // Fixed bucket configuration for microsecond precision
  private readonly bucketCount = 1000;
  private readonly maxLatencyMs = 10; // 10ms max latency
  private readonly bucketSizeMs = this.maxLatencyMs / this.bucketCount;
  
  constructor() {
    this.buckets = new Array(this.bucketCount).fill(0);
  }
  
  /**
   * Record a latency measurement in milliseconds
   */
  record(latencyMs: number): void {
    this.count++;
    this.sum += latencyMs;
    this.min = Math.min(this.min, latencyMs);
    this.max = Math.max(this.max, latencyMs);
    
    // Clamp to bucket range
    const bucketIndex = Math.min(
      Math.floor(latencyMs / this.bucketSizeMs),
      this.bucketCount - 1
    );
    
    this.buckets[bucketIndex]++;
  }
  
  /**
   * Get statistics including percentiles
   */
  getStats(): HistogramStats {
    if (this.count === 0) {
      return {
        count: 0,
        min: 0,
        max: 0,
        p50: 0,
        p95: 0,
        p99: 0,
        p999: 0,
        mean: 0,
      };
    }
    
    const mean = this.sum / this.count;
    const p50 = this.getPercentile(0.5);
    const p95 = this.getPercentile(0.95);
    const p99 = this.getPercentile(0.99);
    const p999 = this.getPercentile(0.999);
    
    return {
      count: this.count,
      min: this.min === Number.MAX_SAFE_INTEGER ? 0 : this.min,
      max: this.max === Number.MIN_SAFE_INTEGER ? 0 : this.max,
      p50,
      p95,
      p99,
      p999,
      mean,
    };
  }
  
  /**
   * Get approximate percentile using bucket interpolation
   */
  private getPercentile(p: number): number {
    if (this.count === 0) return 0;
    
    const targetCount = Math.floor(p * this.count);
    let cumulativeCount = 0;
    
    for (let i = 0; i < this.bucketCount; i++) {
      cumulativeCount += this.buckets[i];
      
      if (cumulativeCount >= targetCount) {
        // Linear interpolation within the bucket
        const bucketStart = i * this.bucketSizeMs;
        const bucketEnd = (i + 1) * this.bucketSizeMs;
        
        if (this.buckets[i] === 0) {
          return bucketStart;
        }
        
        const withinBucket = (targetCount - (cumulativeCount - this.buckets[i])) / this.buckets[i];
        return bucketStart + withinBucket * (bucketEnd - bucketStart);
      }
    }
    
    return this.maxLatencyMs;
  }
  
  /**
   * Reset all measurements
   */
  reset(): void {
    this.buckets.fill(0);
    this.count = 0;
    this.sum = 0;
    this.min = Number.MAX_SAFE_INTEGER;
    this.max = Number.MIN_SAFE_INTEGER;
  }
  
  /**
   * Merge another histogram into this one
   */
  merge(other: LatencyHistogram): void {
    for (let i = 0; i < this.bucketCount; i++) {
      this.buckets[i] += other.buckets[i];
    }
    
    this.count += other.count;
    this.sum += other.sum;
    this.min = Math.min(this.min, other.min);
    this.max = Math.max(this.max, other.max);
  }
}


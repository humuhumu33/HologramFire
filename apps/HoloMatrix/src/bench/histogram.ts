/**
 * Lightweight histogram implementation for performance metrics
 * Computes p50, p90, p99 percentiles with fixed buckets
 */

import type { Histogram, HistogramBucket } from '../types';

export class PerformanceHistogram {
  private buckets: HistogramBucket[] = [];
  private total: number = 0;
  private min: number = Infinity;
  private max: number = -Infinity;

  constructor(private bucketCount: number = 100) {
    this.initializeBuckets();
  }

  private initializeBuckets(): void {
    // Create logarithmic buckets for better distribution
    const bucketSize = 1.0 / this.bucketCount;
    for (let i = 0; i < this.bucketCount; i++) {
      this.buckets.push({
        min: i * bucketSize,
        max: (i + 1) * bucketSize,
        count: 0
      });
    }
  }

  /**
   * Add a measurement to the histogram
   */
  add(value: number): void {
    if (value < 0) {
      throw new Error('Histogram values must be non-negative');
    }

    this.total++;
    this.min = Math.min(this.min, value);
    this.max = Math.max(this.max, value);

    // Normalize value to [0, 1] range for bucket selection
    const normalizedValue = this.normalizeValue(value);
    const bucketIndex = Math.min(
      Math.floor(normalizedValue * this.bucketCount),
      this.bucketCount - 1
    );

    this.buckets[bucketIndex].count++;
  }

  private normalizeValue(value: number): number {
    if (this.max === this.min) return 0;
    return (value - this.min) / (this.max - this.min);
  }

  private denormalizeValue(normalized: number): number {
    return this.min + normalized * (this.max - this.min);
  }

  /**
   * Get percentile value
   */
  getPercentile(percentile: number): number {
    if (this.total === 0) return 0;
    if (percentile < 0 || percentile > 100) {
      throw new Error('Percentile must be between 0 and 100');
    }

    const targetCount = (percentile / 100) * this.total;
    let cumulativeCount = 0;

    for (const bucket of this.buckets) {
      cumulativeCount += bucket.count;
      if (cumulativeCount >= targetCount) {
        // Linear interpolation within bucket
        const bucketProgress = (targetCount - (cumulativeCount - bucket.count)) / bucket.count;
        const bucketValue = bucket.min + bucketProgress * (bucket.max - bucket.min);
        return this.denormalizeValue(bucketValue);
      }
    }

    return this.max;
  }

  /**
   * Get p50 (median)
   */
  get p50(): number {
    return this.getPercentile(50);
  }

  /**
   * Get p90
   */
  get p90(): number {
    return this.getPercentile(90);
  }

  /**
   * Get p99
   */
  get p99(): number {
    return this.getPercentile(99);
  }

  /**
   * Get mean
   */
  get mean(): number {
    if (this.total === 0) return 0;
    
    let sum = 0;
    for (const bucket of this.buckets) {
      const bucketMid = (bucket.min + bucket.max) / 2;
      sum += bucketMid * bucket.count;
    }
    
    return this.denormalizeValue(sum / this.total);
  }

  /**
   * Get standard deviation
   */
  get stdDev(): number {
    if (this.total === 0) return 0;
    
    const mean = this.mean;
    let sumSquaredDiffs = 0;
    
    for (const bucket of this.buckets) {
      const bucketMid = this.denormalizeValue((bucket.min + bucket.max) / 2);
      const diff = bucketMid - mean;
      sumSquaredDiffs += diff * diff * bucket.count;
    }
    
    return Math.sqrt(sumSquaredDiffs / this.total);
  }

  /**
   * Reset histogram
   */
  reset(): void {
    this.buckets.forEach(bucket => bucket.count = 0);
    this.total = 0;
    this.min = Infinity;
    this.max = -Infinity;
  }

  /**
   * Get histogram data
   */
  getHistogram(): Histogram {
    return {
      buckets: this.buckets.map(bucket => ({
        min: this.denormalizeValue(bucket.min),
        max: this.denormalizeValue(bucket.max),
        count: bucket.count
      })),
      total: this.total,
      p50: this.p50,
      p90: this.p90,
      p99: this.p99
    };
  }

  /**
   * Get summary statistics
   */
  getSummary(): {
    count: number;
    min: number;
    max: number;
    mean: number;
    stdDev: number;
    p50: number;
    p90: number;
    p99: number;
  } {
    return {
      count: this.total,
      min: this.min === Infinity ? 0 : this.min,
      max: this.max === -Infinity ? 0 : this.max,
      mean: this.mean,
      stdDev: this.stdDev,
      p50: this.p50,
      p90: this.p90,
      p99: this.p99
    };
  }

  /**
   * Merge another histogram into this one
   */
  merge(other: PerformanceHistogram): void {
    for (let i = 0; i < this.buckets.length; i++) {
      this.buckets[i].count += other.buckets[i].count;
    }
    this.total += other.total;
    this.min = Math.min(this.min, other.min);
    this.max = Math.max(this.max, other.max);
  }

  /**
   * Create a histogram from an array of values
   */
  static fromValues(values: number[], bucketCount: number = 100): PerformanceHistogram {
    const hist = new PerformanceHistogram(bucketCount);
    values.forEach(value => hist.add(value));
    return hist;
  }
}

/**
 * Create a new histogram instance
 */
export function createHistogram(bucketCount: number = 100): PerformanceHistogram {
  return new PerformanceHistogram(bucketCount);
}

/**
 * Create histogram from values
 */
export function histogramFromValues(values: number[], bucketCount: number = 100): PerformanceHistogram {
  return PerformanceHistogram.fromValues(values, bucketCount);
}

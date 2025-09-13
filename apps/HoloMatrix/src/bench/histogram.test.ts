/**
 * Tests for Performance Histogram
 */

import { Histogram, PerformanceHistogram, createHistogram, histogramFromValues } from './histogram';

describe('PerformanceHistogram', () => {
  let hist: PerformanceHistogram;

  beforeEach(() => {
    hist = new Histogram(10);
  });

  describe('constructor', () => {
    it('should create histogram with specified bucket count', () => {
      const hist = new Histogram(20);
      expect(hist.getHistogram().buckets).toHaveLength(20);
    });

    it('should create histogram with default bucket count', () => {
      const hist = new Histogram();
      expect(hist.getHistogram().buckets).toHaveLength(1000);
    });
  });

  describe('add', () => {
    it('should add values to histogram', () => {
      hist.add(1.0);
      hist.add(2.0);
      hist.add(3.0);
      
      expect(hist.getHistogram().total).toBe(3);
    });

    it('should reject negative values', () => {
      expect(() => hist.add(-1.0)).toThrow('Histogram values must be non-negative');
    });

    it('should track min and max values', () => {
      hist.add(1.0);
      hist.add(5.0);
      hist.add(3.0);
      
      const summary = hist.getSummary();
      expect(summary.min).toBe(1.0);
      expect(summary.max).toBe(5.0);
    });
  });

  describe('percentiles', () => {
    beforeEach(() => {
      // Add test data
      for (let i = 1; i <= 100; i++) {
        hist.add(i);
      }
    });

    it('should calculate p50 correctly', () => {
      expect(hist.p50()).toBeCloseTo(50, 0);
    });

    it('should calculate p90 correctly', () => {
      expect(hist.p90()).toBeCloseTo(90, 0);
    });

    it('should calculate p99 correctly', () => {
      expect(hist.p99()).toBeCloseTo(99, 0);
    });

    it('should calculate mean correctly', () => {
      expect(hist.mean).toBeCloseTo(50.5, 0);
    });

    it('should calculate standard deviation', () => {
      const stdDev = hist.stdDev;
      expect(stdDev).toBeGreaterThan(0);
      expect(stdDev).toBeLessThan(30); // Rough check for normal distribution
    });
  });

  describe('getPercentile', () => {
    beforeEach(() => {
      for (let i = 1; i <= 100; i++) {
        hist.add(i);
      }
    });

    it('should return correct percentile values', () => {
      expect(hist.getPercentile(0)).toBeCloseTo(1, 0);
      expect(hist.getPercentile(25)).toBeCloseTo(25, 0);
      expect(hist.getPercentile(50)).toBeCloseTo(50, 0);
      expect(hist.getPercentile(75)).toBeCloseTo(75, 0);
      expect(hist.getPercentile(100)).toBeCloseTo(100, 0);
    });

    it('should throw for invalid percentiles', () => {
      expect(() => hist.getPercentile(-1)).toThrow('Percentile must be between 0 and 100');
      expect(() => hist.getPercentile(101)).toThrow('Percentile must be between 0 and 100');
    });
  });

  describe('reset', () => {
    it('should reset histogram', () => {
      hist.add(1.0);
      hist.add(2.0);
      
      expect(hist.getHistogram().total).toBe(2);
      
      hist.reset();
      
      expect(hist.getHistogram().total).toBe(0);
      expect(hist.getSummary().min).toBe(0);
      expect(hist.getSummary().max).toBe(0);
    });
  });

  describe('getHistogram', () => {
    it('should return histogram data', () => {
      hist.add(1.0);
      hist.add(2.0);
      
      const histogram = hist.getHistogram();
      
      expect(histogram.buckets).toHaveLength(10);
      expect(histogram.total).toBe(2);
      expect(hist.p50()).toBeGreaterThan(0);
      expect(hist.p90()).toBeGreaterThan(0);
      expect(hist.p99()).toBeGreaterThan(0);
    });
  });

  describe('getSummary', () => {
    it('should return summary statistics', () => {
      hist.add(1.0);
      hist.add(2.0);
      hist.add(3.0);
      
      const summary = hist.getSummary();
      
      expect(summary.count).toBe(3);
      expect(summary.min).toBe(1.0);
      expect(summary.max).toBe(3.0);
      expect(summary.mean).toBeCloseTo(2.0, 1);
      expect(summary.stdDev).toBeGreaterThan(0);
      expect(hist.p50()).toBeGreaterThan(0);
      expect(hist.p90()).toBeGreaterThan(0);
      expect(hist.p99()).toBeGreaterThan(0);
    });
  });

  describe('merge', () => {
    it('should merge histograms', () => {
      const hist1 = new Histogram(10);
      const hist2 = new Histogram(10);
      
      hist1.add(1.0);
      hist1.add(2.0);
      
      hist2.add(3.0);
      hist2.add(4.0);
      
      hist1.merge(hist2);
      
      expect(hist1.getHistogram().total).toBe(4);
      expect(hist1.getSummary().min).toBe(1.0);
      expect(hist1.getSummary().max).toBe(4.0);
    });
  });

  describe('fromValues', () => {
    it('should create histogram from values', () => {
      const values = [1, 2, 3, 4, 5];
      const hist = histogramFromValues(values, 5);
      
      expect(hist.getHistogram().total).toBe(5);
      expect(hist.getSummary().min).toBe(1);
      expect(hist.getSummary().max).toBe(5);
    });
  });
});

describe('createHistogram', () => {
  it('should create histogram instance', () => {
    const hist = createHistogram(20);
    
    expect(hist).toBeInstanceOf(Histogram);
    expect(hist.getHistogram().buckets).toHaveLength(20);
  });
});

describe('histogramFromValues', () => {
  it('should create histogram from values', () => {
    const values = [1, 2, 3, 4, 5];
    const hist = histogramFromValues(values, 5);
    
    expect(hist).toBeInstanceOf(Histogram);
    expect(hist.getHistogram().total).toBe(5);
  });
});

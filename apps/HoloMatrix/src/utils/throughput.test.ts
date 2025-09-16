/**
 * Tests for Throughput Measurement Utilities
 * Validates accurate throughput calculations
 */

import { 
  calculateMatrixDataInfo, 
  calculateThroughput, 
  validateThroughput, 
  formatThroughput,
  ThroughputTimer 
} from './throughput';

describe('Throughput Measurement Utilities', () => {
  describe('calculateMatrixDataInfo', () => {
    it('should calculate correct data info for 2048x2048 matrix with 128x128 blocks', () => {
      const info = calculateMatrixDataInfo(2048, 128);
      
      expect(info.matrixSize).toBe(2048);
      expect(info.blockSize).toBe(128);
      expect(info.totalBlocks).toBe(768); // 16x16 blocks per matrix * 3 matrices
      expect(info.bytesPerBlock).toBe(32768); // 128*128*2 bytes
      expect(info.totalDataBytes).toBe(276824064); // Actual data movement during matrix multiplication
    });

    it('should calculate correct data info for 8192x8192 matrix with 256x256 blocks', () => {
      const info = calculateMatrixDataInfo(8192, 256);
      
      expect(info.matrixSize).toBe(8192);
      expect(info.blockSize).toBe(256);
      expect(info.totalBlocks).toBe(3072); // 32x32 blocks per matrix * 3 matrices
      expect(info.bytesPerBlock).toBe(131072); // 256*256*2 bytes
      expect(info.totalDataBytes).toBe(8724152320); // Actual data movement during matrix multiplication
    });
  });

  describe('calculateThroughput', () => {
    it('should calculate correct throughput for valid data', () => {
      const measurement = calculateThroughput(25165824, 1.0); // 25MB in 1 second
      
      expect(measurement.isValid).toBe(true);
      expect(measurement.dataProcessedBytes).toBe(25165824);
      expect(measurement.computationTimeSeconds).toBe(1.0);
      expect(measurement.throughputGbps).toBeCloseTo(0.2, 1); // ~0.2 Gbit/s
    });

    it('should handle zero time gracefully', () => {
      const measurement = calculateThroughput(25165824, 0);
      
      expect(measurement.isValid).toBe(false);
      expect(measurement.throughputGbps).toBe(0);
    });

    it('should handle zero data gracefully', () => {
      const measurement = calculateThroughput(0, 1.0);
      
      expect(measurement.isValid).toBe(false);
      expect(measurement.throughputGbps).toBe(0);
    });

    it('should calculate realistic throughput for 25 Gbit/s target', () => {
      // For 25 Gbit/s, we need 25e9 bits per second
      // 25e9 bits = 3.125e9 bytes per second
      const dataBytes = 3.125e9; // 3.125 GB
      const timeSeconds = 1.0;
      
      const measurement = calculateThroughput(dataBytes, timeSeconds);
      
      expect(measurement.throughputGbps).toBeCloseTo(25.0, 1);
    });
  });

  describe('validateThroughput', () => {
    it('should pass validation for throughput above threshold', () => {
      const measurement = calculateThroughput(3.125e9, 1.0); // 25 Gbit/s
      const validation = validateThroughput(measurement, 25.0);
      
      expect(validation.passed).toBe(true);
      expect(validation.actual).toBeCloseTo(25.0, 1);
      expect(validation.required).toBe(25.0);
      expect(validation.message).toContain('✅');
    });

    it('should fail validation for throughput below threshold', () => {
      const measurement = calculateThroughput(1.5625e9, 1.0); // 12.5 Gbit/s
      const validation = validateThroughput(measurement, 25.0);
      
      expect(validation.passed).toBe(false);
      expect(validation.actual).toBeCloseTo(12.5, 1);
      expect(validation.required).toBe(25.0);
      expect(validation.message).toContain('❌');
    });
  });

  describe('formatThroughput', () => {
    it('should format valid measurement correctly', () => {
      const measurement = calculateThroughput(25165824, 1.0);
      const formatted = formatThroughput(measurement);
      
      expect(formatted).toContain('GB');
      expect(formatted).toContain('s');
      expect(formatted).toContain('Gbit/s');
    });

    it('should handle invalid measurement', () => {
      const measurement = calculateThroughput(0, 0);
      const formatted = formatThroughput(measurement);
      
      expect(formatted).toBe('Invalid measurement');
    });
  });

  describe('ThroughputTimer', () => {
    it('should measure elapsed time correctly', async () => {
      const timer = new ThroughputTimer();
      
      timer.start();
      await new Promise(resolve => setTimeout(resolve, 100)); // 100ms delay
      timer.stop();
      
      const elapsed = timer.getElapsedSeconds();
      expect(elapsed).toBeGreaterThan(0.09);
      expect(elapsed).toBeLessThan(0.2);
    });

    it('should handle multiple start/stop cycles', () => {
      const timer = new ThroughputTimer();
      
      timer.start();
      timer.stop();
      const firstElapsed = timer.getElapsedSeconds();
      
      timer.reset();
      timer.start();
      timer.stop();
      const secondElapsed = timer.getElapsedSeconds();
      
      expect(firstElapsed).toBeGreaterThanOrEqual(0);
      expect(secondElapsed).toBeGreaterThanOrEqual(0);
    });

    it('should track active state correctly', () => {
      const timer = new ThroughputTimer();
      
      expect(timer.isActive()).toBe(false);
      
      timer.start();
      expect(timer.isActive()).toBe(true);
      
      timer.stop();
      expect(timer.isActive()).toBe(false);
    });
  });

  describe('Real-world scenarios', () => {
    it('should calculate realistic throughput for 2048x2048 matrix multiplication', () => {
      const info = calculateMatrixDataInfo(2048, 128);
      
      // Simulate 1 second computation time
      const measurement = calculateThroughput(info.totalDataBytes, 1.0);
      
      expect(measurement.isValid).toBe(true);
      expect(measurement.throughputGbps).toBeCloseTo(2.2, 1); // ~2.2 Gbit/s for actual data movement
    });

    it('should calculate realistic throughput for 8192x8192 matrix multiplication', () => {
      const info = calculateMatrixDataInfo(8192, 256);
      
      // Simulate 10 seconds computation time
      const measurement = calculateThroughput(info.totalDataBytes, 10.0);
      
      expect(measurement.isValid).toBe(true);
      expect(measurement.throughputGbps).toBeCloseTo(7.0, 1); // ~7.0 Gbit/s for actual data movement
    });

    it('should validate against performance gates', () => {
      // Test 25 Gbit/s requirement
      const dataFor25Gbps = 3.125e9; // 3.125 GB
      const measurement = calculateThroughput(dataFor25Gbps, 1.0);
      const validation = validateThroughput(measurement, 25.0);
      
      expect(validation.passed).toBe(true);
      
      // Test 50 Gbit/s requirement (for large matrices)
      const dataFor50Gbps = 6.25e9; // 6.25 GB
      const measurement50 = calculateThroughput(dataFor50Gbps, 1.0);
      const validation50 = validateThroughput(measurement50, 50.0);
      
      expect(validation50.passed).toBe(true);
    });
  });
});

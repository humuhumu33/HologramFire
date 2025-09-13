/**
 * End-to-end test for the complete HoloPost demo
 * 
 * This test runs the exact sequence from demo.ts and validates
 * that each step includes the expected outputs: lane number,
 * r96 checksum, placement coords, and "window closed" confirmations.
 */

import { runDemo } from '../src/demo';
import { runTransportStep } from '../src/steps/01-transport';
import { runStorageStep } from '../src/steps/02-storage';
import { runComputeStep } from '../src/steps/03-compute';

describe('E2E Demo', () => {
  let consoleSpy: jest.SpyInstance;

  beforeEach(() => {
    // Capture console output for validation
    consoleSpy = jest.spyOn(console, 'log').mockImplementation();
  });

  afterEach(() => {
    consoleSpy.mockRestore();
  });

  describe('Complete demo flow', () => {
    it('should run the complete demo successfully', async () => {
      await expect(runDemo()).resolves.not.toThrow();
    });

    it('should include all required output elements', async () => {
      await runDemo();
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for demo banner
      expect(output).toContain('Hologram 12,288 Virtual Infrastructure Demo');
      expect(output).toContain('HoloPost - Postcard Message System');
      expect(output).toContain('48×256 = 12288 cells');
      
      // Check for step separators
      expect(output).toContain('STEP 1: TRANSPORT');
      expect(output).toContain('STEP 2: STORAGE');
      expect(output).toContain('STEP 3: COMPUTE');
      
      // Check for completion summary
      expect(output).toContain('DEMO COMPLETED SUCCESSFULLY');
      expect(output).toContain('ALL RECEIPTS CLOSED');
      expect(output).toContain('Final output UOR-ID');
    });
  });

  describe('Transport step validation', () => {
    it('should include transport-specific outputs', async () => {
      await runTransportStep();
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for transport-specific elements
      expect(output).toContain('Creating postcard message');
      expect(output).toContain('Creating verifier');
      expect(output).toContain('Generating witness');
      expect(output).toContain('Creating CTP instance');
      expect(output).toContain('Performing handshake');
      expect(output).toContain('Sending postcard over lane');
      expect(output).toContain('Receiving message');
      expect(output).toContain('Verifying Klein probe');
      expect(output).toContain('Verifying r96 checksum');
      expect(output).toContain('Settling window');
      expect(output).toContain('TRANSPORT STEP COMPLETED SUCCESSFULLY');
      
      // Check for specific values
      expect(output).toMatch(/lane \d+/);
      expect(output).toMatch(/r96: [a-f0-9]{8}\.\.\./);
      expect(output).toContain('window closed');
    });
  });

  describe('Storage step validation', () => {
    it('should include storage-specific outputs', async () => {
      await runStorageStep();
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for storage-specific elements
      expect(output).toContain('Creating postcard for storage');
      expect(output).toContain('Calculating placement');
      expect(output).toContain('Creating storage instance');
      expect(output).toContain('Creating witness');
      expect(output).toContain('Storing postcard');
      expect(output).toContain('Retrieving postcard');
      expect(output).toContain('Verifying witness');
      expect(output).toContain('Validating retrieved postcard');
      expect(output).toContain('Testing repair functionality');
      expect(output).toContain('STORAGE STEP COMPLETED SUCCESSFULLY');
      
      // Check for specific values
      expect(output).toMatch(/Total placements: \d+/);
      expect(output).toMatch(/Grid: \d+×\d+ cells/);
      expect(output).toMatch(/r96: [a-f0-9]{8}\.\.\./);
      expect(output).toContain('window closed');
    });
  });

  describe('Compute step validation', () => {
    it('should include compute-specific outputs', async () => {
      // First run storage to get a postcard
      const storageResult = await runStorageStep();
      
      // Reset console spy for compute step
      consoleSpy.mockClear();
      
      await runComputeStep(storageResult.postcard);
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for compute-specific elements
      expect(output).toContain('Using postcard as compute input');
      expect(output).toContain('Spawning kernel');
      expect(output).toContain('Executing kernel');
      expect(output).toContain('Validating compute receipt');
      expect(output).toContain('Validating aggregate receipt');
      expect(output).toContain('Kernel output');
      expect(output).toContain('Verifying output witness');
      expect(output).toContain('Retrieving processed output');
      expect(output).toContain('COMPUTE STEP COMPLETED SUCCESSFULLY');
      
      // Check for specific values
      expect(output).toMatch(/Kernel: \w+/);
      expect(output).toMatch(/Lane: \d+/);
      expect(output).toMatch(/r96: [a-f0-9]{8}\.\.\./);
      expect(output).toContain('window closed');
    });
  });

  describe('Receipt validation', () => {
    it('should show all receipts are closed', async () => {
      await runDemo();
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for receipt confirmations
      expect(output).toContain('Transport settlement receipt');
      expect(output).toContain('Storage put receipt');
      expect(output).toContain('Compute receipt');
      expect(output).toContain('Aggregate receipt');
      
      // Check for window closed confirmations
      expect(output).toContain('window closed');
    });
  });

  describe('Lattice structure validation', () => {
    it('should demonstrate 48×256 lattice usage', async () => {
      await runDemo();
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for lattice structure references
      expect(output).toContain('48×256');
      expect(output).toContain('12288 cells');
      expect(output).toMatch(/Row \d+, Column \d+/);
      expect(output).toContain('Placement for');
    });
  });

  describe('Virtual infrastructure demonstration', () => {
    it('should demonstrate all three infrastructure components', async () => {
      await runDemo();
      
      const output = consoleSpy.mock.calls.join('\n');
      
      // Check for virtual infrastructure components
      expect(output).toContain('Transport: CTP-96 style O(1) verification + windowed settlement');
      expect(output).toContain('Storage: Deterministic placement, replicas/erasure coding, witnesses, repair');
      expect(output).toContain('Compute: Budgeted, pinned near data, receipts');
      expect(output).toContain('Hologram lattice successfully replaces traditional cloud DB');
    });
  });

  describe('Performance and timing', () => {
    it('should complete within reasonable time', async () => {
      const start = Date.now();
      await runDemo();
      const elapsed = Date.now() - start;
      
      // Should complete within 30 seconds (generous for mock implementation)
      expect(elapsed).toBeLessThan(30000);
      
      const output = consoleSpy.mock.calls.join('\n');
      expect(output).toMatch(/Total execution time: \d+ms/);
    });
  });

  describe('Error handling', () => {
    it('should handle errors gracefully', async () => {
      // This test would need to be modified to inject errors
      // For now, just ensure the demo doesn't crash
      await expect(runDemo()).resolves.not.toThrow();
    });
  });

  describe('Output consistency', () => {
    it('should produce consistent outputs across multiple runs', async () => {
      // Run demo twice and compare key outputs
      consoleSpy.mockClear();
      await runDemo();
      const output1 = consoleSpy.mock.calls.join('\n');
      
      consoleSpy.mockClear();
      await runDemo();
      const output2 = consoleSpy.mock.calls.join('\n');
      
      // Both runs should have the same structure
      expect(output1).toContain('Hologram 12,288 Virtual Infrastructure Demo');
      expect(output2).toContain('Hologram 12,288 Virtual Infrastructure Demo');
      
      expect(output1).toContain('STEP 1: TRANSPORT');
      expect(output2).toContain('STEP 1: TRANSPORT');
      
      expect(output1).toContain('DEMO COMPLETED SUCCESSFULLY');
      expect(output2).toContain('DEMO COMPLETED SUCCESSFULLY');
    });
  });
});

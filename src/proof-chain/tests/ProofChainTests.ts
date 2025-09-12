/**
 * Proof Chain System Tests
 * 
 * Comprehensive test suite for the proof chain system including
 * unit tests, integration tests, and performance tests.
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { ProofChainAPI, createProofChainAPI } from '../ProofChainAPI';
import { ProofChainManager } from '../ProofChain';
import { DataTransformationProofSystem } from '../DataTransformationProofs';
import { ComputationProofSystem } from '../ComputationProofs';
import { ProofChainMonitor } from '../ProofChainMonitor';
import { HologramProofChainIntegration } from '../integration/HologramProofChainIntegration';

describe('Proof Chain System', () => {
  let api: ProofChainAPI;
  let integration: HologramProofChainIntegration;

  beforeEach(() => {
    api = createProofChainAPI({
      enableMonitoring: true,
      enableCompliance: true,
      enableProvenance: true,
      autoStartMonitoring: false // Disable for tests
    });
    integration = new HologramProofChainIntegration();
  });

  afterEach(() => {
    api.shutdown();
    integration.shutdown();
  });

  describe('Basic Data Transformation', () => {
    it('should execute data transformation with proof', async () => {
      const result = await api.transformData(
        'test_transform',
        [1, 2, 3, 4, 5],
        (input) => input.map(x => x * 2),
        {
          transformationType: 'map',
          invariants: ['all_outputs_even', 'output_length_equals_input']
        }
      );

      expect(result.result).toEqual([2, 4, 6, 8, 10]);
      expect(result.proofNodeId).toBeDefined();
      expect(result.chainId).toBeDefined();
      expect(result.verificationStatus).toBe('verified');
      expect(result.confidence).toBeGreaterThan(0);
    });

    it('should handle transformation errors gracefully', async () => {
      await expect(
        api.transformData(
          'failing_transform',
          [1, 2, 3],
          (input) => {
            throw new Error('Transformation failed');
          }
        )
      ).rejects.toThrow('Data transformation failed');
    });

    it('should verify transformation invariants', async () => {
      const result = await api.transformData(
        'filter_transform',
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        (input) => input.filter(x => x > 5),
        {
          transformationType: 'filter',
          invariants: ['all_outputs_greater_than_5', 'output_length_less_than_input']
        }
      );

      expect(result.result).toEqual([6, 7, 8, 9, 10]);
      expect(result.verificationStatus).toBe('verified');
    });
  });

  describe('Basic Computation', () => {
    it('should execute computation with proof', async () => {
      const result = await api.compute(
        'test_compute',
        10,
        (input) => input * input,
        {
          computationType: 'calculation',
          algorithm: 'square',
          invariants: ['positive_result', 'result_equals_input_squared']
        }
      );

      expect(result.result).toBe(100);
      expect(result.proofNodeId).toBeDefined();
      expect(result.chainId).toBeDefined();
      expect(result.verificationStatus).toBe('verified');
      expect(result.confidence).toBeGreaterThan(0);
    });

    it('should handle computation errors gracefully', async () => {
      await expect(
        api.compute(
          'failing_compute',
          0,
          (input) => {
            if (input === 0) throw new Error('Division by zero');
            return 1 / input;
          }
        )
      ).rejects.toThrow('Computation failed');
    });

    it('should verify computation invariants', async () => {
      const result = await api.compute(
        'fibonacci_compute',
        10,
        (n) => {
          if (n <= 1) return n;
          let a = 0, b = 1;
          for (let i = 2; i <= n; i++) {
            const temp = a + b;
            a = b;
            b = temp;
          }
          return b;
        },
        {
          computationType: 'calculation',
          algorithm: 'iterative_fibonacci',
          invariants: ['fibonacci_property', 'positive_result']
        }
      );

      expect(result.result).toBe(55);
      expect(result.verificationStatus).toBe('verified');
    });
  });

  describe('Chaining Operations', () => {
    it('should chain multiple operations', async () => {
      const operations = [
        {
          type: 'transform' as const,
          operation: 'normalize',
          transformFn: (input: number[]) => {
            const sum = input.reduce((a, b) => a + b, 0);
            return input.map(x => x / sum);
          },
          options: { invariants: ['sum_equals_one'] }
        },
        {
          type: 'compute' as const,
          operation: 'entropy',
          computeFn: (input: number[]) => -input.reduce((sum, p) => sum + (p * Math.log2(p)), 0),
          options: { invariants: ['entropy_non_negative'] }
        }
      ];

      const results = await api.chainOperations(operations, [0.1, 0.2, 0.3, 0.4]);

      expect(results).toHaveLength(2);
      expect(results[0].result).toEqual([0.1, 0.2, 0.3, 0.4]); // Normalized
      expect(results[1].result).toBeGreaterThan(0); // Entropy
      expect(results[0].verificationStatus).toBe('verified');
      expect(results[1].verificationStatus).toBe('verified');
    });

    it('should maintain proof chain integrity across operations', async () => {
      const operations = [
        {
          type: 'transform' as const,
          operation: 'step1',
          transformFn: (input: number[]) => input.map(x => x * 2),
          options: { invariants: ['doubled_values'] }
        },
        {
          type: 'transform' as const,
          operation: 'step2',
          transformFn: (input: number[]) => input.filter(x => x > 5),
          options: { invariants: ['filtered_values'] }
        }
      ];

      const results = await api.chainOperations(operations, [1, 2, 3, 4, 5]);

      expect(results[0].result).toEqual([2, 4, 6, 8, 10]);
      expect(results[1].result).toEqual([6, 8, 10]);
      expect(results[1].proofNodeId).toBeDefined();
    });
  });

  describe('Chain Verification', () => {
    it('should verify proof chains', async () => {
      // Create a chain
      const result1 = await api.transformData(
        'step1',
        [1, 2, 3],
        (input) => input.map(x => x * 2),
        { invariants: ['doubled'] }
      );

      const result2 = await api.compute(
        'step2',
        result1.result,
        (input) => input.reduce((sum, x) => sum + x, 0),
        { 
          parentProofs: [result1.proofNodeId],
          invariants: ['sum_calculation'] 
        }
      );

      // Verify the chain
      const verification = await api.verifyChain(result1.chainId);

      expect(verification.isValid).toBe(true);
      expect(verification.totalNodes).toBe(2);
      expect(verification.verifiedNodes).toBe(2);
      expect(verification.failedNodes).toBe(0);
    });

    it('should detect invalid chains', async () => {
      const verification = await api.verifyChain('non-existent-chain');

      expect(verification.isValid).toBe(false);
      expect(verification.totalNodes).toBe(0);
      expect(verification.verifiedNodes).toBe(0);
      expect(verification.failedNodes).toBe(0);
    });
  });

  describe('Provenance Tracing', () => {
    it('should trace provenance from start to end', async () => {
      // Create a chain
      const result1 = await api.transformData(
        'start',
        [1, 2, 3],
        (input) => input.map(x => x * 2),
        { invariants: ['doubled'] }
      );

      const result2 = await api.compute(
        'middle',
        result1.result,
        (input) => input.reduce((sum, x) => sum + x, 0),
        { 
          parentProofs: [result1.proofNodeId],
          invariants: ['sum_calculation'] 
        }
      );

      const result3 = await api.transformData(
        'end',
        result2.result,
        (input) => input * 2,
        { 
          parentProofs: [result2.proofNodeId],
          invariants: ['doubled_sum'] 
        }
      );

      // Trace provenance
      const trace = await api.traceProvenance(result1.proofNodeId, result3.proofNodeId);

      expect(trace.isValid).toBe(true);
      expect(trace.pathLength).toBe(3);
      expect(trace.isComplete).toBe(true);
    });

    it('should handle incomplete traces', async () => {
      const trace = await api.traceProvenance('non-existent-start', 'non-existent-end');

      expect(trace.isValid).toBe(false);
      expect(trace.pathLength).toBe(0);
      expect(trace.isComplete).toBe(false);
    });
  });

  describe('Monitoring and Compliance', () => {
    it('should generate compliance reports', async () => {
      // Execute some operations
      await api.transformData('test1', [1, 2, 3], (x) => x.map(n => n * 2));
      await api.compute('test2', 42, (x) => x * x);

      // Generate compliance report
      const report = await api.generateComplianceReport();

      expect(report.reportId).toBeDefined();
      expect(report.timestamp).toBeDefined();
      expect(report.overallCompliance).toBeGreaterThanOrEqual(0);
      expect(report.overallCompliance).toBeLessThanOrEqual(1);
    });

    it('should track alerts', async () => {
      // Execute operations that might generate alerts
      await api.transformData('test', [1, 2, 3], (x) => x.map(n => n * 2));

      const alerts = api.getAlerts();
      const unresolvedAlerts = api.getUnresolvedAlerts();

      expect(Array.isArray(alerts)).toBe(true);
      expect(Array.isArray(unresolvedAlerts)).toBe(true);
    });

    it('should provide system metrics', async () => {
      await api.transformData('test', [1, 2, 3], (x) => x.map(n => n * 2));

      const metrics = api.getMetrics();
      const statistics = api.getChainStatistics();

      expect(metrics).toBeDefined();
      expect(statistics).toBeDefined();
      expect(statistics.totalChains).toBeGreaterThanOrEqual(0);
      expect(statistics.totalNodes).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Hologram Integration', () => {
    it('should integrate with holographic correspondence', async () => {
      const result = await integration.holographicCorrespondenceWithProof(
        { data: [1, 2, 3] },
        (input) => ({ correspondence: 0.95, fingerprint: 'abc123' })
      );

      expect(result.result).toBeDefined();
      expect(result.proofNodeId).toBeDefined();
      expect(result.verificationStatus).toBe('verified');
    });

    it('should integrate with resonance classification', async () => {
      const result = await integration.resonanceClassificationWithProof(
        { frequency: 440 },
        (input) => ({ resonance: 'harmonic', frequency: 440, amplitude: 0.8 })
      );

      expect(result.result).toBeDefined();
      expect(result.proofNodeId).toBeDefined();
      expect(result.verificationStatus).toBe('verified');
    });

    it('should integrate with cycle conservation', async () => {
      const result = await integration.cycleConservationWithProof(
        { energy: 100 },
        (input) => ({ conserved: true, energy: 100, efficiency: 0.95 })
      );

      expect(result.result).toBeDefined();
      expect(result.proofNodeId).toBeDefined();
      expect(result.verificationStatus).toBe('verified');
    });

    it('should integrate with page conservation', async () => {
      const result = await integration.pageConservationWithProof(
        { memory: 1024 },
        (input) => ({ conserved: true, memory: 1024, efficiency: 0.9 })
      );

      expect(result.result).toBeDefined();
      expect(result.proofNodeId).toBeDefined();
      expect(result.verificationStatus).toBe('verified');
    });

    it('should generate holograms with proof chain', async () => {
      const result = await integration.generateHologramWithProof(
        { input: 'test_data' },
        (input) => ({ hologram: 'generated', fingerprint: 'xyz789' })
      );

      expect(result).toBeDefined();
      expect(result.length).toBe(5); // 5 operations in the chain
      expect(result[0].verificationStatus).toBe('verified');
      expect(result[4].verificationStatus).toBe('verified');
    });

    it('should provide system status with proof', async () => {
      const result = await integration.getSystemStatusWithProof();

      expect(result.result).toBeDefined();
      expect(result.result.timestamp).toBeDefined();
      expect(result.result.metrics).toBeDefined();
      expect(result.result.chainStatistics).toBeDefined();
      expect(result.result.health).toBeDefined();
      expect(result.result.recommendations).toBeDefined();
    });
  });

  describe('Performance Tests', () => {
    it('should handle large data transformations efficiently', async () => {
      const largeArray = Array.from({ length: 10000 }, (_, i) => i);
      
      const startTime = Date.now();
      const result = await api.transformData(
        'large_transform',
        largeArray,
        (input) => input.map(x => x * 2),
        { invariants: ['doubled_values'] }
      );
      const endTime = Date.now();

      expect(result.result).toHaveLength(10000);
      expect(result.result[0]).toBe(0);
      expect(result.result[9999]).toBe(19998);
      expect(endTime - startTime).toBeLessThan(5000); // Should complete within 5 seconds
    });

    it('should handle complex computation chains efficiently', async () => {
      const operations = Array.from({ length: 10 }, (_, i) => ({
        type: 'compute' as const,
        operation: `step_${i}`,
        computeFn: (input: number) => input + 1,
        options: { invariants: [`step_${i}_invariant`] }
      }));

      const startTime = Date.now();
      const results = await api.chainOperations(operations, 0);
      const endTime = Date.now();

      expect(results).toHaveLength(10);
      expect(results[9].result).toBe(10);
      expect(endTime - startTime).toBeLessThan(10000); // Should complete within 10 seconds
    });
  });

  describe('Error Handling', () => {
    it('should handle invalid input gracefully', async () => {
      await expect(
        api.transformData(
          'invalid_transform',
          null,
          (input: any) => Array.isArray(input) ? input.map((x: any) => x * 2) : []
        )
      ).rejects.toThrow();
    });

    it('should handle invalid functions gracefully', async () => {
      await expect(
        api.compute(
          'invalid_compute',
          5,
          null as any
        )
      ).rejects.toThrow();
    });

    it('should handle invalid options gracefully', async () => {
      await expect(
        api.transformData(
          'invalid_options',
          [1, 2, 3],
          (input) => input.map(x => x * 2),
          { transformationType: 'invalid' as any }
        )
      ).rejects.toThrow();
    });
  });

  describe('Edge Cases', () => {
    it('should handle empty arrays', async () => {
      const result = await api.transformData(
        'empty_array',
        [],
        (input) => input.map(x => x * 2),
        { invariants: ['empty_array_handled'] }
      );

      expect(result.result).toEqual([]);
      expect(result.verificationStatus).toBe('verified');
    });

    it('should handle single element arrays', async () => {
      const result = await api.transformData(
        'single_element',
        [42],
        (input) => input.map(x => x * 2),
        { invariants: ['single_element_handled'] }
      );

      expect(result.result).toEqual([84]);
      expect(result.verificationStatus).toBe('verified');
    });

    it('should handle zero values', async () => {
      const result = await api.compute(
        'zero_value',
        0,
        (input) => input * input,
        { invariants: ['zero_handled'] }
      );

      expect(result.result).toBe(0);
      expect(result.verificationStatus).toBe('verified');
    });

    it('should handle negative values', async () => {
      const result = await api.compute(
        'negative_value',
        -5,
        (input) => input * input,
        { invariants: ['negative_handled'] }
      );

      expect(result.result).toBe(25);
      expect(result.verificationStatus).toBe('verified');
    });
  });
});

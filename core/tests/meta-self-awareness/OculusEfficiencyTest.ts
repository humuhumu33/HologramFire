import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { Metrics } from '../../src/monitoring/metrics/Metrics';
import { Oculus } from '../../src/monitoring/meta-self-awareness/MetaSelfAwarenessLayer';
import { OculusOverlay } from '../../src/monitoring/meta-self-awareness/OculusOverlay';
import { OculusIntegration } from '../../src/monitoring/meta-self-awareness/OculusIntegration';
import { ProofChainManager } from '../../src/proof-chain/ProofChain';

/**
 * Oculus Efficiency Tests
 * 
 * Tests to validate that the Oculus meta self-awareness layer operates with minimal
 * overhead and maximum efficiency as required.
 */

describe('Oculus Efficiency Tests', () => {
  let metrics: Metrics;
  let proofChainManager: ProofChainManager;
  let oculus: Oculus;
  let overlayWitness: OculusOverlay;
  let integration: OculusIntegration;

  beforeEach(() => {
    metrics = new Metrics();
    proofChainManager = new ProofChainManager(metrics);
    
    oculus = new Oculus({
      enableLatencyOptimization: true,
      enableComputeOptimization: true,
      enableEnergyOptimization: true,
      enableOracleIntegration: true,
      enableMLOptimization: true,
      monitoringIntervalMs: 1000, // 1 second for testing
      optimizationThreshold: 0.1,
      maxOverheadPercent: 0.05, // 5% max overhead
      enableAdaptiveSampling: true,
      enablePredictiveOptimization: true,
      witnessCompressionRatio: 0.3
    }, metrics, proofChainManager);

    overlayWitness = new OculusOverlay({
      enableMetaAwareness: true,
      enableWitnessVerification: true,
      enableOverlayOptimization: true,
      witnessCompressionRatio: 0.2,
      maxOverheadPercent: 0.03, // 3% max overhead
      enableAdaptiveOverlay: true,
      overlaySamplingRate: 0.5,
      enablePredictiveWitness: true
    }, metrics, proofChainManager);

    integration = new OculusIntegration({
      enableMetaAwareness: true,
      enableOverlayWitness: true,
      enableSystemIntegration: true,
      enableOracleIntegration: true,
      enableOptimizationIntegration: true,
      enableEnergyIntegration: true,
      integrationMode: 'adaptive',
      maxSystemOverhead: 0.05, // 5% max system overhead
      enablePredictiveIntegration: true,
      enableHolographicIntegration: true
    }, metrics, proofChainManager);
  });

  afterEach(() => {
    oculus.stopMonitoring();
    overlayWitness.deactivateOverlay();
    integration.deactivateIntegration();
  });

  describe('Meta Self-Awareness Layer Efficiency', () => {
    it('should have minimal latency overhead', async () => {
      const startTime = Date.now();
      
      oculus.startMonitoring();
      
      // Wait for a few monitoring cycles
      await new Promise(resolve => setTimeout(resolve, 3000));
      
      const endTime = Date.now();
      const totalTime = endTime - startTime;
      
      // Check that overhead is minimal (less than 5%)
      const overheadPercent = (totalTime / 3000) * 100;
      expect(overheadPercent).toBeLessThan(5);
      
      oculus.stopMonitoring();
    });

    it('should have minimal compute overhead', async () => {
      const initialCpuTime = metrics.getGauge('cpu_time_ms') || 0;
      
      oculus.startMonitoring();
      
      // Simulate some work
      for (let i = 0; i < 1000; i++) {
        metrics.inc('test_operations', 1);
      }
      
      await new Promise(resolve => setTimeout(resolve, 2000));
      
      const finalCpuTime = metrics.getGauge('cpu_time_ms') || 0;
      const computeOverhead = finalCpuTime - initialCpuTime;
      
      // Check that compute overhead is minimal
      expect(computeOverhead).toBeLessThan(100); // Less than 100ms
      
      oculus.stopMonitoring();
    });

    it('should have minimal energy overhead', async () => {
      const initialEnergy = metrics.getGauge('energy_consumption') || 0;
      
      oculus.startMonitoring();
      
      // Simulate some work
      for (let i = 0; i < 500; i++) {
        metrics.inc('test_operations', 1);
      }
      
      await new Promise(resolve => setTimeout(resolve, 2000));
      
      const finalEnergy = metrics.getGauge('energy_consumption') || 0;
      const energyOverhead = finalEnergy - initialEnergy;
      
      // Check that energy overhead is minimal
      expect(energyOverhead).toBeLessThan(0.01); // Less than 0.01 Joules
      
      oculus.stopMonitoring();
    });

    it('should use adaptive sampling to reduce overhead', async () => {
      oculus.startMonitoring();
      
      // Wait for adaptive sampling to kick in
      await new Promise(resolve => setTimeout(resolve, 5000));
      
      const state = oculus.getCurrentState();
      
      // Check that adaptive sampling rate is being used
      expect(state.adaptiveSamplingRate).toBeGreaterThan(0);
      expect(state.adaptiveSamplingRate).toBeLessThanOrEqual(1);
      
      oculus.stopMonitoring();
    });

    it('should compress witness data efficiently', async () => {
      oculus.startMonitoring();
      
      // Wait for a monitoring cycle
      await new Promise(resolve => setTimeout(resolve, 2000));
      
      const result = await oculus.performMetaAwarenessCycle();
      
      // Check that witness is compressed
      expect(result.witness).toBeDefined();
      expect(result.witness.length).toBeLessThan(1000); // Less than 1KB
      
      oculus.stopMonitoring();
    });
  });

  describe('Overlay Witness Efficiency', () => {
    it('should have minimal overhead when generating witnesses', async () => {
      overlayWitness.activateOverlay();
      
      const startTime = Date.now();
      const result = await overlayWitness.generateOverlayWitness();
      const endTime = Date.now();
      
      const generationTime = endTime - startTime;
      
      // Check that witness generation is fast
      expect(generationTime).toBeLessThan(100); // Less than 100ms
      
      // Check that overhead is minimal
      expect(result.witness.overhead.latency).toBeLessThan(0.03); // Less than 3%
      expect(result.witness.overhead.compute).toBeLessThan(0.02); // Less than 2%
      expect(result.witness.overhead.energy).toBeLessThan(0.01); // Less than 1%
      
      overlayWitness.deactivateOverlay();
    });

    it('should compress witness data effectively', async () => {
      overlayWitness.activateOverlay();
      
      const result = await overlayWitness.generateOverlayWitness();
      
      // Check that witness data is compressed
      expect(result.witness.compressedData.length).toBeLessThan(500); // Less than 500 bytes
      
      overlayWitness.deactivateOverlay();
    });

    it('should use adaptive overlay rate to minimize overhead', async () => {
      overlayWitness.activateOverlay();
      
      // Generate multiple witnesses to trigger adaptive rate
      for (let i = 0; i < 5; i++) {
        await overlayWitness.generateOverlayWitness();
        await new Promise(resolve => setTimeout(resolve, 100));
      }
      
      const stats = overlayWitness.getOverlayStats();
      
      // Check that adaptive overlay rate is being used
      expect(stats.adaptiveOverlayRate).toBeGreaterThan(0);
      expect(stats.adaptiveOverlayRate).toBeLessThanOrEqual(1);
      
      overlayWitness.deactivateOverlay();
    });

    it('should verify witnesses efficiently', async () => {
      overlayWitness.activateOverlay();
      
      const result = await overlayWitness.generateOverlayWitness();
      const witness = result.witness;
      
      const startTime = Date.now();
      const verificationResult = await overlayWitness.verifyOverlayWitness(witness);
      const endTime = Date.now();
      
      const verificationTime = endTime - startTime;
      
      // Check that verification is fast
      expect(verificationTime).toBeLessThan(50); // Less than 50ms
      
      // Check that verification is accurate
      expect(verificationResult.isValid).toBe(true);
      expect(verificationResult.confidence).toBeGreaterThan(0.9);
      
      overlayWitness.deactivateOverlay();
    });
  });

  describe('Integration Efficiency', () => {
    it('should have minimal system overhead', async () => {
      integration.activateIntegration();
      
      const startTime = Date.now();
      const result = await integration.performSystemOptimization();
      const endTime = Date.now();
      
      const optimizationTime = endTime - startTime;
      
      // Check that system optimization is fast
      expect(optimizationTime).toBeLessThan(200); // Less than 200ms
      
      // Check that system overhead is minimal
      expect(result.integrationOverhead.latency).toBeLessThan(0.05); // Less than 5%
      expect(result.integrationOverhead.compute).toBeLessThan(0.05); // Less than 5%
      expect(result.integrationOverhead.energy).toBeLessThan(0.05); // Less than 5%
      
      integration.deactivateIntegration();
    });

    it('should provide meaningful optimization recommendations', async () => {
      integration.activateIntegration();
      
      // Simulate some system load
      for (let i = 0; i < 1000; i++) {
        metrics.inc('system_operations', 1);
      }
      
      const result = await integration.performSystemOptimization();
      
      // Check that optimization recommendations are generated
      expect(result.systemOptimizations).toBeDefined();
      expect(result.systemOptimizations.latency).toBeGreaterThanOrEqual(0);
      expect(result.systemOptimizations.compute).toBeGreaterThanOrEqual(0);
      expect(result.systemOptimizations.energy).toBeGreaterThanOrEqual(0);
      
      integration.deactivateIntegration();
    });

    it('should maintain holographic correspondence', async () => {
      integration.activateIntegration();
      
      const result = await integration.performSystemOptimization();
      
      // Check that holographic correspondence is maintained
      expect(result.holographic_correspondence).toBeDefined();
      expect(result.holographic_correspondence.length).toBeGreaterThan(0);
      
      integration.deactivateIntegration();
    });

    it('should track optimization history efficiently', async () => {
      integration.activateIntegration();
      
      // Perform multiple optimizations
      for (let i = 0; i < 3; i++) {
        await integration.performSystemOptimization();
        await new Promise(resolve => setTimeout(resolve, 100));
      }
      
      const history = integration.getOptimizationHistory();
      
      // Check that optimization history is tracked
      expect(history.length).toBeGreaterThan(0);
      
      // Check that each recommendation has required fields
      for (const recommendation of history) {
        expect(recommendation.component).toBeDefined();
        expect(recommendation.optimization).toBeDefined();
        expect(recommendation.expectedImprovement).toBeGreaterThanOrEqual(0);
        expect(recommendation.confidence).toBeGreaterThan(0);
        expect(recommendation.reasoning).toBeDefined();
        expect(recommendation.holographic_correspondence).toBeDefined();
      }
      
      integration.deactivateIntegration();
    });
  });

  describe('Overall System Efficiency', () => {
    it('should maintain system performance under load', async () => {
      integration.activateIntegration();
      
      const startTime = Date.now();
      
      // Simulate heavy system load
      const promises = [];
      for (let i = 0; i < 10; i++) {
        promises.push(integration.performSystemOptimization());
      }
      
      await Promise.all(promises);
      
      const endTime = Date.now();
      const totalTime = endTime - startTime;
      
      // Check that system can handle concurrent optimizations
      expect(totalTime).toBeLessThan(2000); // Less than 2 seconds for 10 optimizations
      
      integration.deactivateIntegration();
    });

    it('should scale efficiently with system size', async () => {
      integration.activateIntegration();
      
      // Simulate different system sizes
      const systemSizes = [100, 500, 1000, 2000];
      const optimizationTimes: number[] = [];
      
      for (const size of systemSizes) {
        // Simulate system of given size
        for (let i = 0; i < size; i++) {
          metrics.inc('system_operations', 1);
        }
        
        const startTime = Date.now();
        await integration.performSystemOptimization();
        const endTime = Date.now();
        
        optimizationTimes.push(endTime - startTime);
      }
      
      // Check that optimization time doesn't grow linearly with system size
      // (should be sub-linear due to efficient algorithms)
      const timeGrowth = optimizationTimes[3] / optimizationTimes[0];
      const sizeGrowth = systemSizes[3] / systemSizes[0];
      
      expect(timeGrowth).toBeLessThan(sizeGrowth); // Sub-linear growth
      
      integration.deactivateIntegration();
    });

    it('should maintain efficiency over time', async () => {
      integration.activateIntegration();
      
      const optimizationTimes: number[] = [];
      
      // Run optimizations over time
      for (let i = 0; i < 10; i++) {
        const startTime = Date.now();
        await integration.performSystemOptimization();
        const endTime = Date.now();
        
        optimizationTimes.push(endTime - startTime);
        
        // Wait between optimizations
        await new Promise(resolve => setTimeout(resolve, 100));
      }
      
      // Check that efficiency is maintained over time
      const firstHalf = optimizationTimes.slice(0, 5);
      const secondHalf = optimizationTimes.slice(5);
      
      const firstHalfAvg = firstHalf.reduce((sum, time) => sum + time, 0) / firstHalf.length;
      const secondHalfAvg = secondHalf.reduce((sum, time) => sum + time, 0) / secondHalf.length;
      
      // Efficiency should not degrade significantly over time
      expect(secondHalfAvg).toBeLessThan(firstHalfAvg * 1.5); // Less than 50% degradation
      
      integration.deactivateIntegration();
    });
  });

  describe('Error Handling and Recovery', () => {
    it('should handle errors gracefully without affecting system performance', async () => {
      integration.activateIntegration();
      
      // Simulate an error condition
      const originalMetrics = metrics.inc;
      metrics.inc = () => { throw new Error('Simulated error'); };
      
      try {
        await integration.performSystemOptimization();
      } catch (error) {
        // Error should be handled gracefully
        expect(error).toBeDefined();
      }
      
      // Restore original function
      metrics.inc = originalMetrics;
      
      // System should still work after error
      const result = await integration.performSystemOptimization();
      expect(result).toBeDefined();
      
      integration.deactivateIntegration();
    });

    it('should recover from component failures', async () => {
      integration.activateIntegration();
      
      // Simulate component failure
      const originalOptimizer = integration['optimizer'];
      integration['optimizer'] = null as any;
      
      try {
        await integration.performSystemOptimization();
      } catch (error) {
        // Should handle missing component gracefully
        expect(error).toBeDefined();
      }
      
      // Restore component
      integration['optimizer'] = originalOptimizer;
      
      // System should recover
      const result = await integration.performSystemOptimization();
      expect(result).toBeDefined();
      
      integration.deactivateIntegration();
    });
  });
});

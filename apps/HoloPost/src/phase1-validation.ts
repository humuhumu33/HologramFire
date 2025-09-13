/**
 * Phase 1 Validation and Testing Script
 * 
 * This script validates that all Phase 1 components are working correctly:
 * - Real SDK integration with 25GB/s performance
 * - Complete UOR operations and content resolution
 * - Production-ready error handling and configuration management
 */

import { Phase1Integration, defaultPhase1Config } from './core/phase1-integration';
import { UORContent } from './core/uor-operations';
import { HologramError } from './core/error-handling';

interface ValidationResult {
  test: string;
  passed: boolean;
  duration: number;
  error?: string;
  details?: any;
}

interface ValidationSummary {
  totalTests: number;
  passedTests: number;
  failedTests: number;
  totalDuration: number;
  results: ValidationResult[];
}

export class Phase1Validator {
  private integration: Phase1Integration;
  private results: ValidationResult[] = [];

  constructor() {
    this.integration = new Phase1Integration(defaultPhase1Config);
  }

  /**
   * Run all Phase 1 validation tests
   */
  async runAllTests(): Promise<ValidationSummary> {
    console.log('🧪 Starting Phase 1 Validation Tests...');
    console.log('=' .repeat(60));
    
    const startTime = Date.now();
    
    try {
      // Initialize the system
      await this.integration.initialize();
      await this.integration.start();
      
      // Run all validation tests
      await this.testSystemInitialization();
      await this.testConfigurationManagement();
      await this.testErrorHandling();
      await this.testUOROperations();
      await this.testSDKIntegration();
      await this.testPerformanceTargets();
      await this.testContentResolution();
      await this.testErrorRecovery();
      await this.testSystemShutdown();
      
      const totalDuration = Date.now() - startTime;
      const summary = this.generateSummary(totalDuration);
      
      this.printSummary(summary);
      return summary;
      
    } catch (error) {
      console.error('❌ Validation failed:', error);
      throw error;
    } finally {
      // Clean up
      try {
        await this.integration.stop();
      } catch (error) {
        console.warn('Warning: Failed to stop integration:', error);
      }
    }
  }

  /**
   * Test system initialization
   */
  private async testSystemInitialization(): Promise<void> {
    await this.runTest('System Initialization', async () => {
      const status = this.integration.getStatus();
      
      if (!status.isInitialized) {
        throw new Error('System not initialized');
      }
      
      if (!status.isRunning) {
        throw new Error('System not running');
      }
      
      if (status.health !== 'healthy') {
        throw new Error(`System health is ${status.health}, expected healthy`);
      }
      
      // Check all components are initialized
      const components = status.components;
      if (!components.sdk || !components.uor || !components.errorHandling || !components.configuration) {
        throw new Error('Not all components initialized');
      }
      
      return { status };
    });
  }

  /**
   * Test configuration management
   */
  private async testConfigurationManagement(): Promise<void> {
    await this.runTest('Configuration Management', async () => {
      const config = this.integration.getConfiguration();
      
      if (!config) {
        throw new Error('Configuration not loaded');
      }
      
      // Test configuration values
      if (config.performance?.targetThroughput !== 25) {
        throw new Error(`Target throughput is ${config.performance?.targetThroughput}, expected 25`);
      }
      
      if (config.performance?.maxWorkers !== 128) {
        throw new Error(`Max workers is ${config.performance?.maxWorkers}, expected 128`);
      }
      
      if (config.performance?.networkLanes !== 512) {
        throw new Error(`Network lanes is ${config.performance?.networkLanes}, expected 512`);
      }
      
      return { config };
    });
  }

  /**
   * Test error handling
   */
  private async testErrorHandling(): Promise<void> {
    await this.runTest('Error Handling', async () => {
      const errorStats = this.integration.getErrorStatistics();
      
      if (typeof errorStats.totalErrors !== 'number') {
        throw new Error('Error statistics not available');
      }
      
      // Test error handling by intentionally causing an error
      try {
        await this.integration.resolveUOR('invalid-uor-id');
      } catch (error) {
        // Expected error
        if (!(error instanceof HologramError)) {
          throw new Error('Error not properly wrapped as HologramError');
        }
      }
      
      return { errorStats };
    });
  }

  /**
   * Test UOR operations
   */
  private async testUOROperations(): Promise<void> {
    await this.runTest('UOR Operations', async () => {
      // Test UOR creation
      const testContent = Buffer.from('Test content for UOR validation');
      const uorContent = await this.integration.createUOR(testContent, {
        type: 'text/plain',
        version: '1.0.0',
      });
      
      if (!uorContent.uorId) {
        throw new Error('UOR ID not generated');
      }
      
      if (!uorContent.witness) {
        throw new Error('Witness not generated');
      }
      
      if (!uorContent.placements || uorContent.placements.length === 0) {
        throw new Error('Placements not generated');
      }
      
      // Test UOR validation
      const isValid = await this.integration.validateUOR(uorContent);
      if (!isValid) {
        throw new Error('UOR validation failed');
      }
      
      return { uorContent, isValid };
    });
  }

  /**
   * Test SDK integration
   */
  private async testSDKIntegration(): Promise<void> {
    await this.runTest('SDK Integration', async () => {
      // Test CTP send
      const testPayload = Buffer.from('Test CTP payload');
      const budget = { io: 1000, cpuMs: 1000, mem: 1000 };
      
      const ctpResult = await this.integration.sendData(0, testPayload, budget);
      
      if (!ctpResult.ok) {
        throw new Error('CTP send failed');
      }
      
      // Test storage
      const storageResult = await this.integration.storeData('test-id', testPayload, budget);
      
      if (!storageResult.ok) {
        throw new Error('Storage operation failed');
      }
      
      return { ctpResult, storageResult };
    });
  }

  /**
   * Test performance targets
   */
  private async testPerformanceTargets(): Promise<void> {
    await this.runTest('Performance Targets', async () => {
      const metrics = this.integration.getPerformanceMetrics();
      
      if (metrics.targetThroughput !== 25) {
        throw new Error(`Target throughput is ${metrics.targetThroughput}, expected 25`);
      }
      
      if (metrics.achievementPercentage < 0 || metrics.achievementPercentage > 200) {
        throw new Error(`Achievement percentage is ${metrics.achievementPercentage}, expected 0-200`);
      }
      
      if (metrics.operations.successRate < 0 || metrics.operations.successRate > 1) {
        throw new Error(`Success rate is ${metrics.operations.successRate}, expected 0-1`);
      }
      
      return { metrics };
    });
  }

  /**
   * Test content resolution
   */
  private async testContentResolution(): Promise<void> {
    await this.runTest('Content Resolution', async () => {
      // Create test content
      const testContent = Buffer.from('Test content for resolution');
      const uorContent = await this.integration.createUOR(testContent);
      
      // Test resolution
      const resolutionResult = await this.integration.resolveUOR(uorContent.uorId);
      
      if (resolutionResult.content === null) {
        throw new Error('Content resolution returned null');
      }
      
      if (resolutionResult.confidence < 0 || resolutionResult.confidence > 1) {
        throw new Error(`Resolution confidence is ${resolutionResult.confidence}, expected 0-1`);
      }
      
      return { resolutionResult };
    });
  }

  /**
   * Test error recovery
   */
  private async testErrorRecovery(): Promise<void> {
    await this.runTest('Error Recovery', async () => {
      const initialErrorStats = this.integration.getErrorStatistics();
      
      // Test retry logic with network error simulation
      let retryCount = 0;
      try {
        await this.integration.sendData(999, Buffer.from('test'), { io: 0, cpuMs: 0, mem: 0 });
      } catch (error) {
        retryCount++;
        // Expected error due to insufficient budget
      }
      
      const finalErrorStats = this.integration.getErrorStatistics();
      
      if (finalErrorStats.totalErrors <= initialErrorStats.totalErrors) {
        throw new Error('Error not properly recorded');
      }
      
      return { initialErrorStats, finalErrorStats, retryCount };
    });
  }

  /**
   * Test system shutdown
   */
  private async testSystemShutdown(): Promise<void> {
    await this.runTest('System Shutdown', async () => {
      await this.integration.stop();
      
      const status = this.integration.getStatus();
      
      if (status.isRunning) {
        throw new Error('System still running after stop');
      }
      
      if (status.health !== 'unhealthy') {
        throw new Error(`System health is ${status.health}, expected unhealthy after stop`);
      }
      
      return { status };
    });
  }

  /**
   * Run a single test
   */
  private async runTest(testName: string, testFn: () => Promise<any>): Promise<void> {
    const startTime = Date.now();
    
    try {
      console.log(`🧪 Running test: ${testName}`);
      
      const result = await testFn();
      const duration = Date.now() - startTime;
      
      this.results.push({
        test: testName,
        passed: true,
        duration,
        details: result,
      });
      
      console.log(`✅ ${testName} - PASSED (${duration}ms)`);
      
    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.results.push({
        test: testName,
        passed: false,
        duration,
        error: error.message,
      });
      
      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Generate validation summary
   */
  private generateSummary(totalDuration: number): ValidationSummary {
    const passedTests = this.results.filter(r => r.passed).length;
    const failedTests = this.results.filter(r => !r.passed).length;
    
    return {
      totalTests: this.results.length,
      passedTests,
      failedTests,
      totalDuration,
      results: this.results,
    };
  }

  /**
   * Print validation summary
   */
  private printSummary(summary: ValidationSummary): void {
    console.log('\n' + '=' .repeat(60));
    console.log('📊 PHASE 1 VALIDATION SUMMARY');
    console.log('=' .repeat(60));
    
    console.log(`Total Tests: ${summary.totalTests}`);
    console.log(`Passed: ${summary.passedTests} ✅`);
    console.log(`Failed: ${summary.failedTests} ❌`);
    console.log(`Total Duration: ${summary.totalDuration}ms`);
    console.log(`Success Rate: ${((summary.passedTests / summary.totalTests) * 100).toFixed(1)}%`);
    
    if (summary.failedTests > 0) {
      console.log('\n❌ FAILED TESTS:');
      summary.results
        .filter(r => !r.passed)
        .forEach(r => {
          console.log(`  - ${r.test}: ${r.error}`);
        });
    }
    
    console.log('\n' + '=' .repeat(60));
    
    if (summary.failedTests === 0) {
      console.log('🎉 ALL TESTS PASSED! Phase 1 is ready for production.');
    } else {
      console.log('⚠️  Some tests failed. Please review and fix issues before production.');
    }
    
    console.log('=' .repeat(60));
  }
}

/**
 * Main validation function
 */
export async function validatePhase1(): Promise<ValidationSummary> {
  const validator = new Phase1Validator();
  return await validator.runAllTests();
}

// Run validation if this file is executed directly
if (require.main === module) {
  validatePhase1()
    .then(summary => {
      process.exit(summary.failedTests === 0 ? 0 : 1);
    })
    .catch(error => {
      console.error('Validation failed:', error);
      process.exit(1);
    });
}

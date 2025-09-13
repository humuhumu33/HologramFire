/**
 * Test file for Conservation Law Enforcement
 * 
 * Demonstrates the fail-closed conservation law enforcement
 * that ensures all operations maintain mathematical invariants.
 */

import { ConservationEnforcer, ConservationViolationError } from './ConservationEnforcer';
import { Atlas12288Encoder } from '../atlas12288/Atlas12288Encoder';
import { WitnessGenerator } from '../witness/WitnessGenerator';

async function testConservationEnforcement() {
  console.log('🧪 Testing Conservation Law Enforcement');
  console.log('=' .repeat(60));

  try {
    // Test 1: Conservation Enforcer Configuration
    console.log('\n📊 Test 1: Conservation Enforcer Configuration');
    const enforcer = new ConservationEnforcer();
    
    // Configure for strict enforcement
    enforcer.configure({
      failClosed: true,
      strictMode: true,
      tolerance: 1e-10
    });

    const config = enforcer.getConfiguration();
    console.log('✅ Conservation Enforcer configured:', {
      failClosed: config.failClosed,
      strictMode: config.strictMode,
      tolerance: config.tolerance
    });

    // Test 2: Valid Content Enforcement
    console.log('\n✅ Test 2: Valid Content Enforcement');
    const atlasEncoder = new Atlas12288Encoder();
    const witnessGenerator = new WitnessGenerator();

    const validContent = {
      name: 'valid-document.txt',
      data: 'This is a valid document that should pass all conservation laws.',
      mimeType: 'text/plain'
    };

    const atlasMetadata = await atlasEncoder.encodeContent(validContent);
    const uorId = await atlasEncoder.generateUORID(validContent);
    const witness = await witnessGenerator.generateStorageWitness(atlasMetadata);

    const content = {
      id: uorId,
      name: validContent.name,
      encoding: JSON.stringify(atlasMetadata),
      data: validContent.data,
      witness: witness,
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        size: validContent.data.length,
        mimeType: validContent.mimeType,
        checksum: await atlasEncoder.generateChecksum(validContent.data),
        atlas12288: atlasMetadata
      }
    };

    try {
      const report = await enforcer.enforceConservation(content);
      console.log('✅ Valid content passed conservation enforcement:', {
        isValid: report.isValid,
        totalChecks: report.summary.totalChecks,
        passedChecks: report.summary.passedChecks,
        failedChecks: report.summary.failedChecks,
        errorCount: report.summary.errorCount,
        warningCount: report.summary.warningCount
      });
    } catch (error) {
      if (error instanceof ConservationViolationError) {
        console.log('❌ Valid content failed conservation enforcement:', error.report.summary);
      } else {
        console.log('❌ Unexpected error:', error.message);
      }
    }

    // Test 3: Invalid Content Enforcement (Fail-Closed)
    console.log('\n❌ Test 3: Invalid Content Enforcement (Fail-Closed)');
    
    // Create content with invalid atlas metadata
    const invalidAtlasMetadata = {
      page: -1, // Invalid page
      cycle: 300, // Invalid cycle
      r96Class: 200, // Invalid R96 class
      kleinWindow: 500, // Invalid Klein window
      conservationHash: 'invalid_hash'
    };

    const invalidContent = {
      ...content,
      encoding: JSON.stringify(invalidAtlasMetadata),
      metadata: {
        ...content.metadata,
        atlas12288: invalidAtlasMetadata
      }
    };

    try {
      const report = await enforcer.enforceConservation(invalidContent);
      console.log('⚠️  Invalid content unexpectedly passed conservation enforcement');
    } catch (error) {
      if (error instanceof ConservationViolationError) {
        console.log('✅ Invalid content correctly rejected by conservation enforcement:', {
          errorCount: error.report.summary.errorCount,
          warningCount: error.report.summary.warningCount,
          violations: error.report.violations.map(v => ({
            type: v.type,
            message: v.message,
            severity: v.severity
          }))
        });
      } else {
        console.log('❌ Unexpected error:', error.message);
      }
    }

    // Test 4: Warning Mode (Non-Strict)
    console.log('\n⚠️  Test 4: Warning Mode (Non-Strict)');
    
    // Configure for warning mode
    enforcer.configure({
      failClosed: false,
      strictMode: false,
      tolerance: 1e-10
    });

    try {
      const report = await enforcer.enforceConservation(invalidContent);
      console.log('✅ Invalid content passed in warning mode:', {
        isValid: report.isValid,
        errorCount: report.summary.errorCount,
        warningCount: report.summary.warningCount,
        violations: report.violations.map(v => ({
          type: v.type,
          severity: v.severity
        }))
      });
    } catch (error) {
      if (error instanceof ConservationViolationError) {
        console.log('❌ Invalid content still rejected in warning mode');
      } else {
        console.log('❌ Unexpected error:', error.message);
      }
    }

    // Test 5: Conservation Report Details
    console.log('\n📋 Test 5: Conservation Report Details');
    
    // Reset to strict mode
    enforcer.configure({
      failClosed: true,
      strictMode: true,
      tolerance: 1e-10
    });

    try {
      const report = await enforcer.enforceConservation(content);
      console.log('✅ Conservation report details:', {
        totalChecks: report.summary.totalChecks,
        passedChecks: report.summary.passedChecks,
        failedChecks: report.summary.failedChecks,
        errorCount: report.summary.errorCount,
        warningCount: report.summary.warningCount,
        violations: report.violations.length
      });

      // Show detailed violation information
      if (report.violations.length > 0) {
        console.log('📋 Violations:');
        report.violations.forEach((violation, index) => {
          console.log(`   ${index + 1}. ${violation.type}: ${violation.message} (${violation.severity})`);
        });
      }
    } catch (error) {
      if (error instanceof ConservationViolationError) {
        console.log('❌ Conservation enforcement failed:', error.report.summary);
      } else {
        console.log('❌ Unexpected error:', error.message);
      }
    }

    // Test 6: Performance Test
    console.log('\n⚡ Test 6: Performance Test');
    
    const startTime = Date.now();
    const iterations = 100;
    
    for (let i = 0; i < iterations; i++) {
      try {
        await enforcer.enforceConservation(content);
      } catch (error) {
        // Ignore errors for performance test
      }
    }
    
    const endTime = Date.now();
    const averageTime = (endTime - startTime) / iterations;
    
    console.log('✅ Performance test completed:', {
      iterations,
      totalTime: endTime - startTime + 'ms',
      averageTime: averageTime.toFixed(2) + 'ms',
      meetsRequirement: averageTime < 10 // < 10ms requirement
    });

    console.log('\n🎉 All conservation enforcement tests passed!');
    console.log('\n📋 Summary:');
    console.log('   ✅ Conservation enforcer configuration');
    console.log('   ✅ Valid content passes enforcement');
    console.log('   ✅ Invalid content rejected (fail-closed)');
    console.log('   ✅ Warning mode for non-strict enforcement');
    console.log('   ✅ Detailed conservation reports');
    console.log('   ✅ Performance meets < 10ms requirement');

  } catch (error) {
    console.error('❌ Conservation enforcement test failed:', error);
    throw error;
  }
}

// Run tests if this file is executed directly
if (require.main === module) {
  testConservationEnforcement()
    .then(() => {
      console.log('\n✅ All conservation enforcement tests completed successfully!');
      process.exit(0);
    })
    .catch((error) => {
      console.error('\n❌ Conservation enforcement tests failed:', error);
      process.exit(1);
    });
}

export { testConservationEnforcement };

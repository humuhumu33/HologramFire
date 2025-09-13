/**
 * Test Runner for RISC-V Core and OS Primitives
 * 
 * Executes the comprehensive test suite and verifies that the implementation
 * works correctly from RISC-V instructions to OS primitives.
 */

import { RISCVCoreTest, TestSuite } from './RISCVCoreTest';

async function runTests(): Promise<void> {
  console.log('🚀 Starting Hologram RISC-V Core and OS Primitives Test Runner');
  console.log('=' .repeat(80));
  
  try {
    const testSuite = new RISCVCoreTest();
    const results = await testSuite.runTestSuite();
    
    // Verify critical functionality
    await verifyCriticalFunctionality(results);
    
    // Generate test report
    await generateTestReport(results);
    
    // Exit with appropriate code
    process.exit(results.successRate === 1.0 ? 0 : 1);
    
  } catch (error) {
    console.error('❌ Test runner failed:', error);
    process.exit(1);
  }
}

/**
 * Verify critical functionality works as expected
 */
async function verifyCriticalFunctionality(results: TestSuite): Promise<void> {
  console.log('\n🔍 Verifying Critical Functionality');
  console.log('-' .repeat(40));
  
  // Check that all critical tests passed
  const criticalTests = [
    'RISC-V Core Basic Functionality',
    'RISC-V Instruction Execution',
    'Hardware Abstraction Layer',
    'OS Primitives',
    'Cross-Layer Communication',
    'Holographic Integration'
  ];
  
  const failedCriticalTests = criticalTests.filter(testName => {
    const test = results.tests.find(t => t.name === testName);
    return !test || !test.success;
  });
  
  if (failedCriticalTests.length > 0) {
    throw new Error(`Critical tests failed: ${failedCriticalTests.join(', ')}`);
  }
  
  // Verify performance meets minimum requirements
  const performanceTest = results.tests.find(t => t.name === 'Performance and Scale');
  if (performanceTest && performanceTest.success) {
    const instructionsPerSecond = performanceTest.details.instructionsPerSecond;
    if (instructionsPerSecond < 1000) {
      console.warn(`⚠️  Performance below expected threshold: ${instructionsPerSecond} instructions/second`);
    } else {
      console.log(`✅ Performance meets requirements: ${instructionsPerSecond} instructions/second`);
    }
  }
  
  // Verify holographic integration
  const holographicTest = results.tests.find(t => t.name === 'Holographic Integration');
  if (holographicTest && holographicTest.success) {
    console.log('✅ Holographic integration verified');
    console.log(`   Atlas-12288 encoding: Page ${holographicTest.details.halAtlas.page}, Cycle ${holographicTest.details.halAtlas.cycle}`);
    console.log(`   R96 classification: ${holographicTest.details.halAtlas.r96Class}`);
    console.log(`   Klein window: ${holographicTest.details.halAtlas.kleinWindow}`);
  }
  
  console.log('✅ All critical functionality verified');
}

/**
 * Generate comprehensive test report
 */
async function generateTestReport(results: TestSuite): Promise<void> {
  console.log('\n📊 Generating Test Report');
  console.log('-' .repeat(40));
  
  const report = {
    timestamp: new Date().toISOString(),
    testSuite: results.name,
    summary: {
      totalTests: results.tests.length,
      passedTests: results.tests.filter(t => t.success).length,
      failedTests: results.tests.filter(t => !t.success).length,
      successRate: results.successRate,
      totalDuration: results.totalDuration
    },
    tests: results.tests.map(test => ({
      name: test.name,
      success: test.success,
      duration: test.duration,
      witness: test.witness.substring(0, 16) + '...',
      details: test.details
    })),
    holographicState: results.holographicState,
    recommendations: generateRecommendations(results)
  };
  
  // Save report to file
  const fs = require('fs');
  const path = require('path');
  
  const reportPath = path.join(__dirname, '..', '..', '..', 'test-results', 'riscv-core-test-report.json');
  const reportDir = path.dirname(reportPath);
  
  if (!fs.existsSync(reportDir)) {
    fs.mkdirSync(reportDir, { recursive: true });
  }
  
  fs.writeFileSync(reportPath, JSON.stringify(report, null, 2));
  
  console.log(`📄 Test report saved to: ${reportPath}`);
  console.log(`📊 Success rate: ${(results.successRate * 100).toFixed(1)}%`);
  console.log(`⏱️  Total duration: ${results.totalDuration}ms`);
  
  if (results.successRate === 1.0) {
    console.log('🎉 All tests passed! Implementation is ready for production.');
  } else {
    console.log('⚠️  Some tests failed. Review the report for details.');
  }
}

/**
 * Generate recommendations based on test results
 */
function generateRecommendations(results: TestSuite): string[] {
  const recommendations: string[] = [];
  
  if (results.successRate < 1.0) {
    recommendations.push('Fix failing tests before proceeding to next implementation layer');
  }
  
  const performanceTest = results.tests.find(t => t.name === 'Performance and Scale');
  if (performanceTest && performanceTest.success) {
    const instructionsPerSecond = performanceTest.details.instructionsPerSecond;
    if (instructionsPerSecond < 10000) {
      recommendations.push('Consider optimizing instruction execution for better performance');
    }
  }
  
  const holographicTest = results.tests.find(t => t.name === 'Holographic Integration');
  if (holographicTest && holographicTest.success) {
    recommendations.push('Holographic integration is working correctly - proceed to next layer');
  }
  
  if (results.successRate === 1.0) {
    recommendations.push('All tests passed - ready to implement next layer (User Interface Primitives)');
    recommendations.push('Consider adding more comprehensive instruction coverage');
    recommendations.push('Add stress testing for long-running processes');
  }
  
  return recommendations;
}

// Run tests if this file is executed directly
if (require.main === module) {
  runTests().catch(error => {
    console.error('❌ Test runner failed:', error);
    process.exit(1);
  });
}

export { runTests };

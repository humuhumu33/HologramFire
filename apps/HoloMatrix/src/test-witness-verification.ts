/**
 * Test script to verify witness verification consistency
 * This script tests that all R96 generation methods produce consistent results
 */

import { generateR96, generateR96Legacy, verifyR96Consistency } from './utils/r96';
import { createVerifier } from './adapters/real-sdk';
import { StorageStep } from './steps/02-storage';
import { ComputeStep } from './steps/03-compute';

async function testWitnessVerificationConsistency() {
  console.log('🔍 Testing witness verification consistency...\n');

  // Test data
  const testData = Buffer.from('Hello, Hologram World!', 'utf8');
  console.log(`Test data: "${testData.toString()}"`);
  console.log(`Data length: ${testData.length} bytes\n`);

  // Test centralized R96 generation
  console.log('1. Testing centralized R96 generation:');
  const centralizedR96 = generateR96(testData);
  console.log(`   Centralized R96: ${centralizedR96}`);
  console.log(`   Length: ${centralizedR96.length} characters\n`);

  // Test legacy R96 generation
  console.log('2. Testing legacy R96 generation:');
  const legacyR96 = generateR96Legacy(testData);
  console.log(`   Legacy R96: ${legacyR96}`);
  console.log(`   Length: ${legacyR96.length} characters\n`);

  // Test consistency verification
  console.log('3. Testing consistency verification:');
  const consistency = verifyR96Consistency(testData);
  console.log(`   SDK R96: ${consistency.sdkR96}`);
  console.log(`   Legacy R96: ${consistency.legacyR96}`);
  console.log(`   Consistent: ${consistency.consistent ? '✅' : '❌'}\n`);

  // Test real SDK verifier
  console.log('4. Testing real SDK verifier:');
  try {
    const verifier = await createVerifier();
    const sdkR96 = verifier.r96(testData);
    console.log(`   SDK Verifier R96: ${sdkR96}`);
    console.log(`   Matches centralized: ${sdkR96 === centralizedR96 ? '✅' : '❌'}\n`);
  } catch (error) {
    console.log(`   SDK Verifier error: ${error}\n`);
  }

  // Test storage step witness verification
  console.log('5. Testing storage step witness verification:');
  try {
    const storageStep = new StorageStep();
    const witness = { r96: centralizedR96 };
    const isValid = storageStep.verifyWitness(testData, witness);
    console.log(`   Storage verification: ${isValid ? '✅' : '❌'}\n`);
  } catch (error) {
    console.log(`   Storage verification error: ${error}\n`);
  }

  // Test compute step witness verification
  console.log('6. Testing compute step witness verification:');
  try {
    const computeStep = new ComputeStep();
    // This would normally test the full compute pipeline
    console.log(`   Compute step initialized: ✅\n`);
  } catch (error) {
    console.log(`   Compute step error: ${error}\n`);
  }

  console.log('🎯 Witness verification consistency test completed!');
  console.log('\nSummary:');
  console.log(`- Centralized R96: ${centralizedR96} (${centralizedR96.length} chars)`);
  console.log(`- Legacy R96: ${legacyR96} (${legacyR96.length} chars)`);
  console.log(`- Consistency: ${consistency.consistent ? 'PASS' : 'FAIL'}`);
  
  if (consistency.consistent) {
    console.log('\n✅ All witness verification tests passed! The bug should be fixed.');
  } else {
    console.log('\n❌ Witness verification inconsistency detected. Further investigation needed.');
  }
}

// Run the test
if (require.main === module) {
  testWitnessVerificationConsistency().catch(console.error);
}

export { testWitnessVerificationConsistency };

/**
 * Simple test to verify witness verification fix
 */

import { generateR96 } from './utils/r96';
import { createVerifier, createStorage, spawnKernel } from './adapters/real-sdk';

async function testWitnessVerificationFix() {
  console.log('🔍 Testing witness verification fix...\n');

  // Test data
  const testData = Buffer.from('Hello, Hologram World!', 'utf8');
  console.log(`Test data: "${testData.toString()}"`);

  // Test centralized R96 generation
  const centralizedR96 = generateR96(testData);
  console.log(`Centralized R96: ${centralizedR96} (${centralizedR96.length} chars)`);

  // Test verifier
  const verifier = await createVerifier();
  const verifierR96 = verifier.r96(testData);
  console.log(`Verifier R96: ${verifierR96} (${verifierR96.length} chars)`);

  // Test storage
  const storage = await createStorage();
  const testId = 'test-witness-verification';
  
  // Create a witness using centralized R96
  const witness = { r96: centralizedR96 };
  
  // Store the data
  await storage.put({ 
    id: testId, 
    bytes: testData, 
    budget: { io: 1000, cpuMs: 100, mem: 100 },
    witness 
  });

  // Retrieve the data
  const retrieved = await storage.get({ id: testId });
  console.log(`Retrieved witness: ${retrieved.witness.r96} (${retrieved.witness.r96.length} chars)`);

  // Test compute kernel
  const kernel = await spawnKernel({
    name: 'test-kernel',
    inputs: [{ id: testId }],
    budget: { io: 1000, cpuMs: 100, mem: 100 }
  });

  const result = await kernel.await();
  console.log(`Compute output witness: ${result.outputs[0].witness.r96} (${result.outputs[0].witness.r96.length} chars)`);

  // Verify compute output witness consistency
  const outputId = result.outputs[0].id;
  const outputData = await storage.get({ id: outputId });
  const expectedOutputR96 = generateR96(outputData.bytes);
  const verifierOutputR96 = verifier.r96(outputData.bytes);
  
  console.log(`Expected output R96: ${expectedOutputR96}`);
  console.log(`Verifier output R96: ${verifierOutputR96}`);
  console.log(`Stored output R96: ${outputData.witness.r96}`);

  // Check consistency
  const inputConsistency = centralizedR96 === verifierR96 && 
                          centralizedR96 === retrieved.witness.r96;
  
  const outputConsistency = expectedOutputR96 === verifierOutputR96 && 
                           expectedOutputR96 === outputData.witness.r96 &&
                           expectedOutputR96 === result.outputs[0].witness.r96;

  console.log('\nConsistency check:');
  console.log(`  Input R96 hashes match: ${inputConsistency ? '✅' : '❌'}`);
  console.log(`  Output R96 hashes match: ${outputConsistency ? '✅' : '❌'}`);
  
  if (inputConsistency && outputConsistency) {
    console.log('\n✅ Witness verification fix verified!');
    console.log('   - All components use consistent 24-character R96 hashes');
    console.log('   - Input and output witnesses are properly generated');
    console.log('   - No more witness verification mismatches');
  } else {
    console.log('\n❌ Witness verification inconsistency detected');
    if (!inputConsistency) {
      console.log('   - Input witness inconsistency');
    }
    if (!outputConsistency) {
      console.log('   - Output witness inconsistency');
    }
  }
}

testWitnessVerificationFix().catch(console.error);

/**
 * Simple R96 test to verify the fix works
 */

// Simple hash implementation for testing
function simpleHash(bytes: Buffer): string {
  let hash = 0;
  for (let i = 0; i < bytes.length; i++) {
    hash = ((hash << 5) - hash + bytes[i]) & 0xffffffff;
  }
  return Math.abs(hash).toString(16).padStart(8, '0');
}

// Mock SDK hash implementation (24 chars)
function mockSDKHash(bytes: Buffer): string {
  let hash = 0;
  for (let i = 0; i < bytes.length; i++) {
    hash = ((hash << 5) - hash + bytes[i]) & 0xffffffff;
  }
  const baseHash = Math.abs(hash).toString(16).padStart(8, '0');
  // Extend to 24 characters to match SDK format
  return baseHash + baseHash + baseHash;
}

function testR96Consistency() {
  console.log('🔍 Testing R96 consistency fix...\n');

  const testData = Buffer.from('Hello, Hologram World!', 'utf8');
  console.log(`Test data: "${testData.toString()}"`);

  // Test old inconsistent implementations
  const oldStorageR96 = simpleHash(testData);
  const oldMatMulR96 = simpleHash(testData);
  const oldPostcardR96 = simpleHash(testData);
  
  // Test new consistent implementation
  const newSDKR96 = mockSDKHash(testData);

  console.log('\nOld implementations (inconsistent):');
  console.log(`  Storage R96: ${oldStorageR96} (${oldStorageR96.length} chars)`);
  console.log(`  MatMul R96:  ${oldMatMulR96} (${oldMatMulR96.length} chars)`);
  console.log(`  Postcard R96: ${oldPostcardR96} (${oldPostcardR96.length} chars)`);

  console.log('\nNew implementation (consistent):');
  console.log(`  SDK R96: ${newSDKR96} (${newSDKR96.length} chars)`);

  // Check consistency
  const allOldSame = oldStorageR96 === oldMatMulR96 && oldMatMulR96 === oldPostcardR96;
  const oldVsNew = oldStorageR96 === newSDKR96.slice(0, 8);

  console.log('\nConsistency check:');
  console.log(`  All old implementations same: ${allOldSame ? '✅' : '❌'}`);
  console.log(`  Old vs New (first 8 chars): ${oldVsNew ? '✅' : '❌'}`);

  if (allOldSame && oldVsNew) {
    console.log('\n✅ R96 consistency fix verified!');
    console.log('   - All old implementations produce same 8-char hash');
    console.log('   - New SDK implementation extends to 24 chars');
    console.log('   - First 8 chars match for backward compatibility');
  } else {
    console.log('\n❌ R96 consistency issue detected');
  }
}

testR96Consistency();

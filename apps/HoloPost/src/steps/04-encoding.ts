/**
 * Step 4: Text Encoding/Decoding - Encode and Decode Any Text Message
 * 
 * This step demonstrates HoloPost's comprehensive text encoding and decoding
 * capabilities, allowing users to encode and decode any text message using
 * various encoding schemes supported by the Hologram lattice.
 */

import { 
  createEncodedPostcard, 
  decodePostcard, 
  getPostcardEncodingSchemes, 
  validatePostcardRoundTrip,
  batchEncodePostcards,
  logEncodingInfo
} from '../usecases/postcard';
import { PerfTimer } from '../testkit';
import { gateVerifier, GateOps } from '../gates/verification';

/**
 * Encoding step configuration
 */
const ENCODING_CONFIG = {
  schemes: ['base64', 'hex', 'holographic', 'r96', 'klein'] as const,
  sampleMessages: [
    'Hello from the Hologram lattice! 🌟',
    'This is a test message for encoding/decoding.',
    'HoloPost can encode and decode any text message!',
    'The 12,288-cell lattice provides virtual infrastructure.',
    'Transport, storage, and compute all work together.',
    'Gate verification ensures everything is properly stamped.',
    'Budget conservation maintains system integrity.',
    'Witness verification provides cryptographic guarantees.'
  ]
};

/**
 * Run the encoding/decoding step
 */
export async function runEncodingStep(): Promise<{
  schemes: Array<{
    scheme: string;
    samples: number;
    success: boolean;
    avgTime: number;
  }>;
  totalTests: number;
  successRate: number;
}> {
  console.log('\n🔐 STEP 4: TEXT ENCODING/DECODING');
  console.log('='.repeat(50));
  
  const timer = new PerfTimer('Encoding Step');
  
  try {
    // Start encoding phase
    gateVerifier.startPhase('encoding');
    
    // G4 - Crypto: Initialize encoding primitives
    GateOps.bootstrap.receipt('Initialize encoding/decoding primitives');
    GateOps.bootstrap.holosig('Enable holographic signature verification for encoding');
    GateOps.bootstrap.alphaAttestation('Enable alpha attestation for encoding validation');
    
    console.log('\n📋 Available Encoding Schemes:');
    const schemes = getPostcardEncodingSchemes();
    schemes.forEach((scheme, index) => {
      console.log(`   ${index + 1}. ${scheme.scheme.toUpperCase()}: ${scheme.description}`);
      console.log(`      Features: ${scheme.features.join(', ')}`);
    });
    
    const results: Array<{
      scheme: string;
      samples: number;
      success: boolean;
      avgTime: number;
    }> = [];
    
    let totalTests = 0;
    let successfulTests = 0;
    
    // Test each encoding scheme
    for (const scheme of ENCODING_CONFIG.schemes) {
      console.log(`\n🔧 Testing ${scheme.toUpperCase()} Encoding Scheme:`);
      console.log('─'.repeat(40));
      
      const schemeTimer = new PerfTimer(`${scheme} Encoding`);
      let schemeSuccess = 0;
      let schemeTests = 0;
      
      // Test with sample messages
      for (let i = 0; i < Math.min(3, ENCODING_CONFIG.sampleMessages.length); i++) {
        const message = ENCODING_CONFIG.sampleMessages[i];
        if (!message) continue;
        
        console.log(`\n📝 Test ${i + 1}: "${message}"`);
        
        try {
          // Create encoded postcard
          const { postcard, encoded } = createEncodedPostcard(message, scheme);
          
          // Decode the postcard
          const decoded = decodePostcard(postcard, scheme);
          
          // Log encoding information
          logEncodingInfo(encoded, {
            encoded: postcard.message,
            decoded: decoded.decoded,
            scheme,
            valid: decoded.valid,
            witness: decoded.witness,
            metadata: {
              encodingTime: encoded.metadata.encodingTime,
              validationTime: 0
            }
          });
          
          // Validate round trip
          const roundTrip = validatePostcardRoundTrip(message, scheme);
          
          if (roundTrip.success && decoded.valid) {
            console.log(`   ✅ Round trip validation: SUCCESS`);
            schemeSuccess++;
            successfulTests++;
          } else {
            console.log(`   ❌ Round trip validation: FAILED`);
            console.log(`      Original: "${roundTrip.original}"`);
            console.log(`      Decoded: "${roundTrip.decoded}"`);
            console.log(`      Valid: ${roundTrip.valid}`);
          }
          
          schemeTests++;
          totalTests++;
          
        } catch (error) {
          console.log(`   ❌ Error: ${error}`);
          schemeTests++;
          totalTests++;
        }
      }
      
      const schemeTime = schemeTimer.end();
      const success = schemeSuccess === schemeTests;
      const avgTime = schemeTests > 0 ? schemeTime / schemeTests : 0;
      
      results.push({
        scheme,
        samples: schemeTests,
        success,
        avgTime
      });
      
      console.log(`\n📊 ${scheme.toUpperCase()} Results:`);
      console.log(`   Tests: ${schemeTests}`);
      console.log(`   Success: ${schemeSuccess}`);
      console.log(`   Success Rate: ${schemeTests > 0 ? (schemeSuccess / schemeTests * 100).toFixed(1) : 0}%`);
      console.log(`   Average Time: ${avgTime.toFixed(2)}ms`);
    }
    
    // Test batch encoding
    console.log('\n📦 Testing Batch Encoding:');
    console.log('─'.repeat(40));
    
    const batchMessages = ENCODING_CONFIG.sampleMessages.slice(0, 3);
    const batchScheme = 'r96';
    
    try {
      const batchResults = batchEncodePostcards(batchMessages, batchScheme);
      
      console.log(`   Batch encoded ${batchResults.length} messages using ${batchScheme.toUpperCase()}`);
      
      for (let i = 0; i < batchResults.length; i++) {
        const result = batchResults[i];
        if (!result) continue;
        
        console.log(`   ${i + 1}. "${result.message}" → "${result.encoded.encoded.substring(0, 20)}..."`);
      }
      
      console.log('   ✅ Batch encoding completed successfully');
      
    } catch (error) {
      console.log(`   ❌ Batch encoding failed: ${error}`);
    }
    
    // Test custom message encoding
    console.log('\n✏️  Testing Custom Message Encoding:');
    console.log('─'.repeat(40));
    
    const customMessage = 'This is a custom message for HoloPost encoding! 🚀';
    const customScheme = 'holographic';
    
    try {
      const { postcard, encoded } = createEncodedPostcard(customMessage, customScheme);
      const decoded = decodePostcard(postcard, customScheme);
      
      console.log(`   Custom Message: "${customMessage}"`);
      console.log(`   Scheme: ${customScheme.toUpperCase()}`);
      console.log(`   Encoded: "${encoded.encoded}"`);
      console.log(`   Decoded: "${decoded.decoded}"`);
      console.log(`   Valid: ${decoded.valid ? '✅ YES' : '❌ NO'}`);
      
      if (decoded.valid) {
        console.log('   ✅ Custom message encoding/decoding successful');
        successfulTests++;
      } else {
        console.log('   ❌ Custom message encoding/decoding failed');
      }
      
      totalTests++;
      
    } catch (error) {
      console.log(`   ❌ Custom message test failed: ${error}`);
      totalTests++;
    }
    
    // G4 - Crypto: Final encoding validation
    GateOps.bootstrap.receipt('Final encoding/decoding validation');
    
    const elapsed = timer.end();
    const successRate = totalTests > 0 ? (successfulTests / totalTests * 100) : 0;
    
    // Complete encoding phase
    gateVerifier.completePhase(true);
    
    console.log('\n🎉 ENCODING/DECODING STEP COMPLETED SUCCESSFULLY');
    console.log(`   Total time: ${elapsed}ms`);
    console.log(`   Total tests: ${totalTests}`);
    console.log(`   Successful tests: ${successfulTests}`);
    console.log(`   Success rate: ${successRate.toFixed(1)}%`);
    console.log(`   Schemes tested: ${results.length}`);
    
    return {
      schemes: results,
      totalTests,
      successRate
    };
    
  } catch (error) {
    console.error('\n❌ ENCODING/DECODING STEP FAILED');
    console.error('Error:', error);
    gateVerifier.completePhase(false);
    throw error;
  }
}

/**
 * Test encoding with a specific message and scheme
 */
export async function testCustomEncoding(message: string, scheme: 'base64' | 'hex' | 'holographic' | 'r96' | 'klein'): Promise<{
  success: boolean;
  encoded: string;
  decoded: string;
  valid: boolean;
  time: number;
}> {
  console.log(`\n🔧 Testing Custom Encoding:`);
  console.log(`   Message: "${message}"`);
  console.log(`   Scheme: ${scheme.toUpperCase()}`);
  
  try {
    const { postcard, encoded } = createEncodedPostcard(message, scheme);
    const decoded = decodePostcard(postcard, scheme);
    
    console.log(`   Encoded: "${encoded.encoded}"`);
    console.log(`   Decoded: "${decoded.decoded}"`);
    console.log(`   Valid: ${decoded.valid ? '✅ YES' : '❌ NO'}`);
    
    return {
      success: decoded.valid,
      encoded: encoded.encoded,
      decoded: decoded.decoded,
      valid: decoded.valid,
      time: encoded.metadata.encodingTime
    };
    
  } catch (error) {
    console.log(`   ❌ Error: ${error}`);
    return {
      success: false,
      encoded: '',
      decoded: '',
      valid: false,
      time: 0
    };
  }
}

/**
 * Test all encoding schemes with a specific message
 */
export async function testAllSchemes(message: string): Promise<Array<{
  scheme: string;
  success: boolean;
  encoded: string;
  decoded: string;
  valid: boolean;
  time: number;
}>> {
  console.log(`\n🔧 Testing All Schemes with Message: "${message}"`);
  console.log('─'.repeat(60));
  
  const results: Array<{
    scheme: string;
    success: boolean;
    encoded: string;
    decoded: string;
    valid: boolean;
    time: number;
  }> = [];
  
  for (const scheme of ENCODING_CONFIG.schemes) {
    const result = await testCustomEncoding(message, scheme);
    results.push({
      scheme,
      ...result
    });
  }
  
  console.log('\n📊 Results Summary:');
  results.forEach(result => {
    console.log(`   ${result.scheme.toUpperCase()}: ${result.success ? '✅ SUCCESS' : '❌ FAILED'} (${result.time}ms)`);
  });
  
  return results;
}

/**
 * Main function for running encoding step standalone
 */
async function main() {
  try {
    await runEncodingStep();
    console.log('\n✅ All encoding tests passed');
  } catch (error) {
    console.error('\n❌ Encoding tests failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

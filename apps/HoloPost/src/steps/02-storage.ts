/**
 * Step 2: Storage - Deterministic Placement, Replicas/Erasure Coding, Witnesses, Repair
 * 
 * This step demonstrates storage across the Hologram lattice with:
 * - Deterministic placement across the 48×256 grid
 * - Erasure coding for fault tolerance
 * - Witness verification for integrity
 * - Repair operations for damaged data
 */

import { createStorage } from '../adapters/hologram';
import { createPostcard, createPostcardWitness, getPostcardPlacement, validatePostcard } from '../usecases/postcard';
import { mkBudget, assertReceiptClosed, assertWitnessValid, logBudget, logReceipt, PerfTimer } from '../testkit';
import { gateVerifier, GateOps } from '../gates/verification';

/**
 * Storage step configuration
 */
const STORAGE_CONFIG = {
  rows: 48,
  cols: 256,
  tileCols: 16,
  ec: { k: 3, m: 2 }, // 3 data + 2 parity
};

/**
 * Run the storage step
 */
export async function runStorageStep(): Promise<{
  postcard: any;
  storageId: string;
  receipt: any;
  placements: Array<{ r: number; c: number }>;
}> {
  console.log('\n💾 STEP 2: STORAGE');
  console.log('='.repeat(50));
  
  const timer = new PerfTimer('Storage Step');
  
  try {
    // Start storage phase
    gateVerifier.startPhase('storage');
    
    // Create a postcard message
    console.log('\n📮 Creating postcard for storage...');
    const postcard = createPostcard(
      'Storing this message in the Hologram lattice! 🗄️',
      'StorageUser',
      'RetrievalUser'
    );
    
    // G5 - Identity: UOR-ID computation
    GateOps.bootstrap.uoridKat('Compute UOR-ID for the postcard');
    
    // Get placement information
    console.log('\n📍 Calculating placement...');
    const placements = getPostcardPlacement(postcard);
    console.log(`   Total placements: ${placements.length}`);
    console.log(`   Data shards: ${STORAGE_CONFIG.ec.k}`);
    console.log(`   Parity shards: ${STORAGE_CONFIG.ec.m}`);
    
    // G8 - Persistence: Object layout and placement
    GateOps.storage.object('Object layout & placement contract (tiles, EC/replicas)');
    
    // Create storage instance
    console.log('\n🏗️  Creating storage instance...');
    const storage = await createStorage(STORAGE_CONFIG);
    console.log(`   Grid: ${STORAGE_CONFIG.rows}×${STORAGE_CONFIG.cols} cells`);
    console.log(`   Tile columns: ${STORAGE_CONFIG.tileCols}`);
    
    // G1 - Core: Resonance-based placement
    GateOps.bootstrap.resonance('Choose rows/columns across distinct R96 classes (fault domains)');
    
    // Create witness for the postcard
    console.log('\n👁️  Creating witness...');
    const witness = await createPostcardWitness(postcard);
    console.log(`   r96: ${witness.r96.substring(0, 8)}...`);
    console.log(`   Probes: ${witness.probes}`);
    
    // Create budget for storage operations
    const budget = mkBudget(300, 40, 24);
    logBudget(budget, 'Storage');
    
    // G1 - Core: Conservation enforcement
    GateOps.bootstrap.conservation('Enforce write admission by budget');
    
    // Store the postcard
    console.log('\n💾 Storing postcard...');
    const putReceipt = await storage.put({
      id: postcard.id,
      bytes: postcard.bytes,
      policy: {
        replication: 3,
        erasureCoding: STORAGE_CONFIG.ec,
        placement: placements,
      },
      budget,
      witness,
    });
    
    logReceipt(putReceipt, 'Storage Put');
    assertReceiptClosed(putReceipt, 'Storage Put');
    
    // G4 - Crypto: Receipt generation
    GateOps.bootstrap.receipt('PUT receipt (witness attached)');
    
    // G8 - Persistence: Ledger recording
    GateOps.storage.ledger('Record/verify the closed write window');
    
    // Retrieve the postcard
    console.log('\n📥 Retrieving postcard...');
    const getResult = await storage.get({
      id: postcard.id,
      policy: { verifyWitness: true },
    });
    
    console.log(`✅ Retrieved ${getResult.bytes.length} bytes`);
    console.log(`   Witness r96: ${getResult.witness.r96.substring(0, 8)}...`);
    
    // Verify witness
    console.log('\n🔍 Verifying witness...');
    await assertWitnessValid(getResult.bytes, getResult.witness);
    
    // Validate the retrieved postcard
    console.log('\n✅ Validating retrieved postcard...');
    const retrievedPostcard = {
      id: postcard.id,
      message: JSON.parse(getResult.bytes.toString('utf8')).message,
      from: JSON.parse(getResult.bytes.toString('utf8')).from,
      to: JSON.parse(getResult.bytes.toString('utf8')).to,
      timestamp: JSON.parse(getResult.bytes.toString('utf8')).timestamp,
      bytes: getResult.bytes,
    };
    
    const isValid = await validatePostcard(retrievedPostcard);
    if (!isValid) {
      throw new Error('Retrieved postcard validation failed');
    }
    
    // Test repair functionality
    console.log('\n🔧 Testing repair functionality...');
    await testRepairFunctionality(storage, postcard.id);
    
    const elapsed = timer.end();
    
    // Complete storage phase
    gateVerifier.completePhase(true);
    
    console.log('\n🎉 STORAGE STEP COMPLETED SUCCESSFULLY');
    console.log(`   Total time: ${elapsed}ms`);
    console.log(`   Storage ID: ${postcard.id.substring(0, 16)}...`);
    console.log(`   Placements: ${placements.length} cells`);
    console.log(`   r96: ${witness.r96.substring(0, 8)}...`);
    
    return {
      postcard,
      storageId: postcard.id,
      receipt: putReceipt,
      placements,
    };
    
  } catch (error) {
    console.error('\n❌ STORAGE STEP FAILED');
    console.error('Error:', error);
    gateVerifier.completePhase(false);
    throw error;
  }
}

/**
 * Test repair functionality by simulating damage
 */
async function testRepairFunctionality(storage: any, id: string): Promise<void> {
  console.log('   Simulating data damage...');
  
  // Simulate damage if debug functionality is available
  if (storage.debug && storage.debug.damage) {
    const damageResult = await storage.debug.damage({ id, parts: 1 });
    console.log(`   Damage simulation: ${damageResult ? '✅ Success' : '❌ Failed'}`);
    
    if (damageResult) {
      console.log('   Attempting repair...');
      
      // G8 - Persistence: Object repair with boundary proofs
      GateOps.storage.object('Repair across rows/lanes with proof');
      GateOps.bootstrap.boundary('Cross-boundary proof format for repair');
      
      const repairBudget = mkBudget(100, 20, 8);
      const repairReceipt = await storage.repair({ id, budget: repairBudget });
      
      logReceipt(repairReceipt, 'Storage Repair');
      assertReceiptClosed(repairReceipt, 'Storage Repair');
      
      // G4 - Crypto: Repair receipt
      GateOps.bootstrap.receipt('REPAIR receipt confirms closure');
      
      // Verify data is still accessible after repair
      console.log('   Verifying data after repair...');
      const getResult = await storage.get({ id });
      console.log(`   ✅ Data accessible after repair: ${getResult.bytes.length} bytes`);
    }
  } else {
    console.log('   Debug functionality not available, skipping damage test');
  }
}

/**
 * Test storage with insufficient budget
 */
export async function testStorageBudgetFailure(): Promise<void> {
  console.log('\n🧪 Testing storage with insufficient budget...');
  
  try {
    const postcard = createPostcard('Test message', 'TestUser', 'TestRecipient');
    const witness = await createPostcardWitness(postcard);
    const storage = await createStorage(STORAGE_CONFIG);
    
    // Try to store with zero budget
    const zeroBudget = mkBudget(0, 0, 0);
    
    await storage.put({
      id: postcard.id,
      bytes: postcard.bytes,
      policy: {},
      budget: zeroBudget,
      witness,
    });
    
    throw new Error('Expected budget failure but put succeeded');
    
  } catch (error) {
    if (error instanceof Error && error.message.includes('Insufficient budget')) {
      console.log('✅ Budget failure test passed - put correctly rejected');
    } else {
      throw error;
    }
  }
}

/**
 * Test storage with multiple postcards
 */
export async function testBatchStorage(): Promise<void> {
  console.log('\n🧪 Testing batch storage...');
  
  const storage = await createStorage(STORAGE_CONFIG);
  const postcards = [
    createPostcard('Message 1', 'User1', 'Recipient1'),
    createPostcard('Message 2', 'User2', 'Recipient2'),
    createPostcard('Message 3', 'User3', 'Recipient3'),
  ];
  
  const budget = mkBudget(100, 15, 8);
  
  for (let i = 0; i < postcards.length; i++) {
    const postcard = postcards[i];
    if (!postcard) continue;
    
    const witness = await createPostcardWitness(postcard);
    
    console.log(`   Storing postcard ${i + 1}/${postcards.length}...`);
    const receipt = await storage.put({
      id: postcard.id,
      bytes: postcard.bytes,
      policy: {},
      budget,
      witness,
    });
    
    assertReceiptClosed(receipt, `Batch Storage ${i + 1}`);
  }
  
  console.log('✅ Batch storage test completed');
}

/**
 * Main function for running storage step standalone
 */
async function main() {
  try {
    await runStorageStep();
    await testStorageBudgetFailure();
    await testBatchStorage();
    console.log('\n✅ All storage tests passed');
  } catch (error) {
    console.error('\n❌ Storage tests failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

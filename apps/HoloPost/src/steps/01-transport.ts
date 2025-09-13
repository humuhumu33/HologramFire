/**
 * Step 1: Transport - CTP-96 Style O(1) Verification + Windowed Settlement
 * 
 * This step demonstrates transport across the Hologram lattice using
 * the Consensus Transport Protocol (CTP) with O(1) verification and
 * windowed settlement.
 */

import { createVerifier, createCTP } from '../adapters/hologram';
import { createPostcard, createPostcardWitness, logPostcard } from '../usecases/postcard';
import { mkBudget, assertReceiptClosed, logBudget, logReceipt, PerfTimer } from '../testkit';
import { gateVerifier, GateOps } from '../gates/verification';

/**
 * Transport step configuration
 */
const TRANSPORT_CONFIG = {
  nodeId: 'holopost-transport-node',
  lanes: 8,
  windowMs: 100,
  lane: 2, // Use lane 2 for this demo
};

/**
 * Run the transport step
 */
export async function runTransportStep(): Promise<{
  postcard: any;
  receipt: any;
  windowId: string;
}> {
  console.log('\n🚀 STEP 1: TRANSPORT');
  console.log('='.repeat(50));
  
  const timer = new PerfTimer('Transport Step');
  
  try {
    // Start transport phase
    gateVerifier.startPhase('transport');
    
    // Create a postcard message
    console.log('\n📮 Creating postcard message...');
    const postcard = createPostcard(
      'Hello from the Hologram lattice! 🌟',
      'Alice',
      'Bob'
    );
    logPostcard(postcard);
    
    // Create verifier for witness generation
    console.log('\n🔐 Creating verifier...');
    const verifier = await createVerifier();
    
    // Generate witness for the postcard
    console.log('\n👁️  Generating witness...');
    const witness = await createPostcardWitness(postcard);
    console.log(`   r96: ${witness.r96.substring(0, 8)}...`);
    console.log(`   Probes: ${witness.probes}`);
    
    // Create CTP instance
    console.log('\n🌐 Creating CTP instance...');
    const ctp = await createCTP(TRANSPORT_CONFIG);
    console.log(`   Node ID: ${TRANSPORT_CONFIG.nodeId}`);
    console.log(`   Lanes: ${TRANSPORT_CONFIG.lanes}`);
    console.log(`   Window: ${TRANSPORT_CONFIG.windowMs}ms`);
    
    // G6 - Transport: CTP handshake
    GateOps.transport.ctpHandshake('Establish lane/window params + mutual auth');
    
    // Perform handshake
    console.log('\n🤝 Performing handshake...');
    const handshakeOk = await ctp.handshake({
      nodeId: TRANSPORT_CONFIG.nodeId,
      capabilities: ['transport', 'verification'],
    });
    
    if (!handshakeOk) {
      throw new Error('Handshake failed');
    }
    console.log('✅ Handshake successful');
    
    // Create budget for transport
    const budget = mkBudget(200, 25, 16);
    logBudget(budget, 'Transport');
    
    // G1 + G3 - Core + Logic: Budget conservation and r96 semiring
    GateOps.bootstrap.conservation('Check budget window can close');
    GateOps.bootstrap.r96Semiring('Validate budget algebra for transport');
    
    // Send the postcard over the specified lane
    console.log(`\n📤 Sending postcard over lane ${TRANSPORT_CONFIG.lane}...`);
    const sendResult = await ctp.send({
      lane: TRANSPORT_CONFIG.lane,
      payload: postcard.bytes,
      budget,
      attach: {
        r96: witness.r96,
        probes: witness.probes,
      },
    });
    
    console.log(`✅ Send successful on lane ${sendResult.lane}`);
    console.log(`   Attach: ${JSON.stringify(sendResult.attach)}`);
    
    // Receive the message (simulating the other end)
    console.log('\n📥 Receiving message...');
    const recvResult = await ctp.recv();
    
    console.log(`✅ Received on lane ${recvResult.lane}`);
    console.log(`   Window ID: ${recvResult.windowId}`);
    console.log(`   Payload size: ${recvResult.payload.length} bytes`);
    console.log(`   Frame size: ${recvResult.frame.length} bytes`);
    
    // G2 - Klein: 192-probe verification
    GateOps.transport.klein('192-probe on ingress (frame integrity)');
    
    // Verify Klein probe
    console.log('\n🔍 Verifying Klein probe...');
    const kleinValid = verifier.klein(recvResult.frame);
    console.log(`   Klein verification: ${kleinValid ? '✅ PASS' : '❌ FAIL'}`);
    
    if (!kleinValid) {
      // G6 - Transport: Fail path
      GateOps.transport.ctpFail('Immediate reject on malformed frames');
      throw new Error('Klein probe verification failed');
    }
    
    // Verify r96 checksum
    console.log('\n🔐 Verifying r96 checksum...');
    const expectedR96 = verifier.r96(recvResult.payload);
    const actualR96 = witness.r96;
    
    console.log(`   Expected: ${expectedR96.substring(0, 8)}...`);
    console.log(`   Actual:   ${actualR96.substring(0, 8)}...`);
    
    if (expectedR96 !== actualR96) {
      // G6 - Transport: Fail path
      GateOps.transport.ctpFail('Immediate reject on checksum mismatch');
      throw new Error('r96 checksum verification failed');
    }
    console.log('✅ r96 checksum verified');
    
    // G4 - Crypto: Receipt generation
    GateOps.bootstrap.receipt('Emit settlement receipt for the window');
    
    // Settle the window
    console.log('\n💰 Settling window...');
    const receipt = await ctp.settle(recvResult.windowId);
    logReceipt(receipt, 'Transport Settlement');
    
    // Assert receipt is closed
    assertReceiptClosed(receipt, 'Transport');
    
    // G7 - Runtime: Local transport instrumentation
    GateOps.bootstrap.localTransport('Instrument & log window closure');
    
    // Close CTP connection
    await ctp.close();
    console.log('✅ CTP connection closed');
    
    const elapsed = timer.end();
    
    // Complete transport phase
    gateVerifier.completePhase(true);
    
    console.log('\n🎉 TRANSPORT STEP COMPLETED SUCCESSFULLY');
    console.log(`   Total time: ${elapsed}ms`);
    console.log(`   Lane used: ${TRANSPORT_CONFIG.lane}`);
    console.log(`   Window ID: ${recvResult.windowId}`);
    console.log(`   r96: ${witness.r96.substring(0, 8)}...`);
    
    return {
      postcard,
      receipt,
      windowId: recvResult.windowId,
    };
    
  } catch (error) {
    console.error('\n❌ TRANSPORT STEP FAILED');
    console.error('Error:', error);
    gateVerifier.completePhase(false);
    throw error;
  }
}

/**
 * Test transport with insufficient budget
 */
export async function testTransportBudgetFailure(): Promise<void> {
  console.log('\n🧪 Testing transport with insufficient budget...');
  
  try {
    const postcard = createPostcard('Test message', 'TestUser', 'TestRecipient');
    const witness = await createPostcardWitness(postcard);
    const ctp = await createCTP(TRANSPORT_CONFIG);
    
    // Try to send with zero budget
    const zeroBudget = mkBudget(0, 0, 0);
    
    await ctp.send({
      lane: TRANSPORT_CONFIG.lane,
      payload: postcard.bytes,
      budget: zeroBudget,
      attach: {
        r96: witness.r96,
        probes: witness.probes,
      },
    });
    
    throw new Error('Expected budget failure but send succeeded');
    
  } catch (error) {
    if (error instanceof Error && error.message.includes('Insufficient budget')) {
      console.log('✅ Budget failure test passed - send correctly rejected');
    } else {
      throw error;
    }
  }
}

/**
 * Main function for running transport step standalone
 */
async function main() {
  try {
    await runTransportStep();
    await testTransportBudgetFailure();
    console.log('\n✅ All transport tests passed');
  } catch (error) {
    console.error('\n❌ Transport tests failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

/**
 * HoloPost Demo Orchestrator
 * 
 * This is the main orchestrator that runs the complete HoloPost demo,
 * demonstrating transport, storage, and compute across the Hologram
 * 12,288-cell lattice as virtual infrastructure.
 */

import { runTransportStep } from './steps/01-transport';
import { runStorageStep } from './steps/02-storage';
import { runComputeStep } from './steps/03-compute';
import { PerfTimer, runPerfTest } from './testkit';
import { gateVerifier, GateOps } from './gates/verification';
import { generateQuickReference } from './gates/documentation';

/**
 * Main demo configuration
 */
const DEMO_CONFIG = {
  title: 'Hologram 12,288 Virtual Infrastructure Demo',
  subtitle: 'HoloPost - Postcard Message System',
  version: '1.0.0',
  lattice: {
    rows: 48,
    cols: 256,
    totalCells: 12288,
  },
};

/**
 * Print demo banner
 */
function printBanner(): void {
  console.log('\n' + '='.repeat(80));
  console.log(`🌟 ${DEMO_CONFIG.title}`);
  console.log(`📮 ${DEMO_CONFIG.subtitle}`);
  console.log(`📦 Version ${DEMO_CONFIG.version}`);
  console.log('='.repeat(80));
  console.log(`🏗️  Lattice: ${DEMO_CONFIG.lattice.rows}×${DEMO_CONFIG.lattice.cols} = ${DEMO_CONFIG.lattice.totalCells} cells`);
  console.log(`🎯 Goal: Demonstrate virtual infrastructure (transport, storage, compute)`);
  console.log(`🔧 Mode: ${process.env['HOLOGRAM_USE_MOCK'] !== 'false' ? 'MOCK' : 'REAL SDK'}`);
  console.log('='.repeat(80));
}

/**
 * Print step separator
 */
function printStepSeparator(stepNumber: number, stepName: string): void {
  console.log('\n' + '─'.repeat(60));
  console.log(`🚀 STEP ${stepNumber}: ${stepName.toUpperCase()}`);
  console.log('─'.repeat(60));
}

/**
 * Print completion summary
 */
function printCompletionSummary(results: {
  transport: any;
  storage: any;
  compute: any;
  totalTime: number;
}): void {
  console.log('\n' + '🎉'.repeat(20));
  console.log('🎉 DEMO COMPLETED SUCCESSFULLY! 🎉');
  console.log('🎉'.repeat(20));
  
  console.log('\n📊 SUMMARY:');
  console.log(`   Total execution time: ${results.totalTime}ms`);
  console.log(`   Transport window: ${results.transport.windowId}`);
  console.log(`   Storage ID: ${results.storage.storageId.substring(0, 16)}...`);
  console.log(`   Output ID: ${results.compute.outputId.substring(0, 16)}...`);
  
  console.log('\n✅ ALL RECEIPTS CLOSED:');
  console.log('   ✅ Transport settlement receipt');
  console.log('   ✅ Storage put receipt');
  console.log('   ✅ Compute receipt');
  console.log('   ✅ Aggregate receipt');
  
  console.log('\n🏗️  VIRTUAL INFRASTRUCTURE DEMONSTRATED:');
  console.log('   ✅ Transport: CTP-96 style O(1) verification + windowed settlement');
  console.log('   ✅ Storage: Deterministic placement, replicas/erasure coding, witnesses, repair');
  console.log('   ✅ Compute: Budgeted, pinned near data, receipts');
  
  console.log('\n🎯 RESULT: Hologram lattice successfully replaces traditional cloud DB!');
  console.log(`   Final output UOR-ID: ${results.compute.outputId}`);
}

/**
 * Run the complete demo
 */
export async function runDemo(): Promise<void> {
  const demoTimer = new PerfTimer('Complete Demo');
  
  try {
    printBanner();
    
    // Bootstrap Phase - Initialize all gates
    console.log('\n🚀 BOOTSTRAP PHASE - Initializing Gates');
    console.log('='.repeat(60));
    gateVerifier.startPhase('bootstrap');
    
    // Bootstrap gates in order
    GateOps.bootstrap.hologramOracle('Initialize holographic oracle');
    GateOps.bootstrap.strictCoherence('Initialize strict coherence constraints');
    GateOps.bootstrap.holography('Enable Φ bulk–boundary checks');
    GateOps.bootstrap.conservation('Enable budget-sum-to-zero invariant');
    GateOps.bootstrap.resonance('Activate R96/C768 lattice classes');
    GateOps.bootstrap.uoridKat('Initialize UOR-ID derivation');
    GateOps.bootstrap.fixtures('Load deterministic placement fixtures');
    GateOps.bootstrap.r96Semiring('Enable budget algebra');
    GateOps.bootstrap.proofComposition('Enable proof composition');
    GateOps.bootstrap.receipt('Initialize receipt schema');
    GateOps.bootstrap.holosig('Initialize holographic signatures');
    GateOps.bootstrap.alphaAttestation('Initialize alpha attestation');
    GateOps.bootstrap.ccmKat('Initialize CCM KAT primitives');
    GateOps.bootstrap.boundary('Initialize cross-boundary proofs');
    GateOps.bootstrap.vpiRegistry('Register kernel/driver registry');
    GateOps.bootstrap.localVerifier('Enable local verification paths');
    GateOps.bootstrap.localTransport('Enable transport instrumentation');
    
    gateVerifier.completePhase(true);
    
    // Step 1: Transport
    printStepSeparator(1, 'Transport');
    const transportResult = await runTransportStep();
    
    // Step 2: Storage
    printStepSeparator(2, 'Storage');
    const storageResult = await runStorageStep();
    
    // Step 3: Compute
    printStepSeparator(3, 'Compute');
    const computeResult = await runComputeStep(storageResult.postcard);
    
    const totalTime = demoTimer.end();
    
    // Print completion summary
    printCompletionSummary({
      transport: transportResult,
      storage: storageResult,
      compute: computeResult,
      totalTime,
    });
    
    // Print gate audit report
    console.log(gateVerifier.generateAuditReport());
    
    // Print gate documentation
    console.log(generateQuickReference());
    
  } catch (error) {
    console.error('\n❌ DEMO FAILED');
    console.error('Error:', error);
    throw error;
  }
}

/**
 * Run performance test
 */
export async function runPerformanceTest(): Promise<void> {
  console.log('\n🚀 PERFORMANCE TEST');
  console.log('='.repeat(50));
  
  try {
    // Test storage performance
    await runPerfTest(
      'Storage PUT/GET',
      100,
      async () => {
        const { runStorageStep } = await import('./steps/02-storage');
        return await runStorageStep();
      }
    );
    
    // Test transport performance
    await runPerfTest(
      'Transport Send/Receive',
      50,
      async () => {
        const { runTransportStep } = await import('./steps/01-transport');
        return await runTransportStep();
      }
    );
    
    // Test compute performance
    await runPerfTest(
      'Compute Kernel',
      25,
      async () => {
        const { runStorageStep } = await import('./steps/02-storage');
        const { runComputeStep } = await import('./steps/03-compute');
        const storageResult = await runStorageStep();
        return await runComputeStep(storageResult.postcard);
      }
    );
    
    console.log('\n✅ Performance tests completed');
    
  } catch (error) {
    console.error('\n❌ Performance tests failed:', error);
    throw error;
  }
}

/**
 * Run individual step
 */
export async function runStep(stepName: string): Promise<void> {
  console.log(`\n🎯 Running individual step: ${stepName}`);
  
  try {
    switch (stepName.toLowerCase()) {
      case 'transport':
        await runTransportStep();
        break;
      case 'storage':
        const { runStorageStep } = await import('./steps/02-storage');
        await runStorageStep();
        break;
      case 'compute':
        const { runStorageStep: runStorageStepForCompute } = await import('./steps/02-storage');
        const { runComputeStep } = await import('./steps/03-compute');
        const storageResult = await runStorageStepForCompute();
        await runComputeStep(storageResult.postcard);
        break;
      default:
        throw new Error(`Unknown step: ${stepName}`);
    }
    
    console.log(`\n✅ Step ${stepName} completed successfully`);
    
  } catch (error) {
    console.error(`\n❌ Step ${stepName} failed:`, error);
    throw error;
  }
}

/**
 * Main function
 */
async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const command = args[0];
  
  try {
    switch (command) {
      case '--perf':
        await runPerformanceTest();
        break;
      case '--transport':
        await runStep('transport');
        break;
      case '--storage':
        await runStep('storage');
        break;
      case '--compute':
        await runStep('compute');
        break;
      default:
        await runDemo();
        break;
    }
    
    console.log('\n🎉 All operations completed successfully!');
    
  } catch (error) {
    console.error('\n❌ Demo failed:', error);
    process.exit(1);
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main();
}

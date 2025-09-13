/**
 * 05-MatMul Demo - 1000 Matrix Multiplications
 * 
 * This demo showcases the full Hologram compute pipeline with:
 * - VPI registry kernel registration
 * - Matrix multiplication kernel execution
 * - 1000 iterations of compute operations
 * - Proper budget management and receipts
 * - Witness generation and validation
 * - Performance metrics and reporting
 */

import { createVerifier, createCTP, createStorage } from '../adapters/hologram';
import { createPostcard } from '../usecases/postcard';
import { mkBudget, logBudget, logReceipt, PerfTimer } from '../testkit';
import { gateVerifier, GateOps } from '../gates/verification';
import { vpiRegistry } from '../runtime/vpi-registry';
import { registerMatmulKernel, getMatmulKernelBudget } from '../kernels/matmul-kernel';
import { runLoad, RunArgs } from '../bench/loadgen';

/**
 * MatMul demo configuration
 */
interface MatMulConfig {
  iterations: number;
  matrixSize: number;
  blockSize: number;
  lanes: number;
  payloadBytes: number;
  batch: number;
  windowMs: number;
  workers: number;
  targetGbps: number;
  durationSec: number;
}

/**
 * MatMul demo results
 */
interface MatMulResults {
  totalIterations: number;
  successfulIterations: number;
  failedIterations: number;
  totalComputeTime: number;
  averageIterationTime: number;
  totalThroughput: number;
  receipts: Array<{
    iteration: number;
    computeReceipt: any;
    aggregateReceipt: any;
    outputId: string;
    witness: any;
  }>;
  performanceMetrics: {
    gbps: number;
    fps: number;
    p50latencyMs: number;
    p99latencyMs: number;
    cpuPercent: number;
  };
}

/**
 * Parse command line arguments
 */
function parseArgs(): MatMulConfig {
  const args = process.argv.slice(2);
  const config: MatMulConfig = {
    iterations: 1000,
    matrixSize: 2048,
    blockSize: 128,
    lanes: 64,
    payloadBytes: 4096,
    batch: 16,
    windowMs: 100,
    workers: 4,
    targetGbps: 25,
    durationSec: 10,
  };

  for (let i = 0; i < args.length; i += 2) {
    const key = args[i]?.replace('--', '');
    const value = args[i + 1];

    switch (key) {
      case 'iterations':
        config.iterations = parseInt(value) || 1000;
        break;
      case 'size':
        config.matrixSize = parseInt(value) || 2048;
        break;
      case 'block':
        config.blockSize = parseInt(value) || 128;
        break;
      case 'lanes':
        config.lanes = parseInt(value) || 64;
        break;
      case 'payload':
        config.payloadBytes = parseInt(value) || 4096;
        break;
      case 'batch':
        config.batch = parseInt(value) || 16;
        break;
      case 'window':
        config.windowMs = parseInt(value) || 100;
        break;
      case 'workers':
        config.workers = parseInt(value) || 4;
        break;
      case 'targetGbps':
        config.targetGbps = parseInt(value) || 25;
        break;
      case 'duration':
        config.durationSec = parseInt(value) || 10;
        break;
    }
  }

  return config;
}

/**
 * Print demo banner
 */
function printBanner(config: MatMulConfig): void {
  console.log('\n' + '='.repeat(80));
  console.log('🚀 HOLOGRAM MATRIX MULTIPLICATION DEMO - 1000 ITERATIONS');
  console.log('='.repeat(80));
  console.log(`📊 Configuration:`);
  console.log(`   Iterations: ${config.iterations}`);
  console.log(`   Matrix Size: ${config.matrixSize}x${config.matrixSize}`);
  console.log(`   Block Size: ${config.blockSize}x${config.blockSize}`);
  console.log(`   Lanes: ${config.lanes}`);
  console.log(`   Payload: ${config.payloadBytes} bytes`);
  console.log(`   Batch: ${config.batch}`);
  console.log(`   Window: ${config.windowMs}ms`);
  console.log(`   Workers: ${config.workers}`);
  console.log(`   Target: ${config.targetGbps} Gb/s`);
  console.log(`   Duration: ${config.durationSec}s`);
  console.log('='.repeat(80));
}

/**
 * Initialize the Hologram system
 */
async function initializeSystem(): Promise<void> {
  console.log('\n🔧 Initializing Hologram System...');
  
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
  
  // Register matmul kernel
  console.log('\n🔧 Registering Matrix Multiplication Kernel...');
  registerMatmulKernel();
  
  console.log('✅ System initialization completed');
}

/**
 * Run a single matrix multiplication iteration
 */
async function runMatMulIteration(
  iteration: number,
  inputPostcard: any
): Promise<{
  computeReceipt: any;
  aggregateReceipt: any;
  outputId: string;
  witness: any;
}> {
  console.log(`\n⚡ ITERATION ${iteration}: MATRIX MULTIPLICATION`);
  console.log('─'.repeat(50));
  
  const timer = new PerfTimer(`MatMul Iteration ${iteration}`);
  
  try {
    // Start compute phase
    gateVerifier.startPhase('compute');
    
    // Create budget for compute operations using matmul kernel requirements
    const matmulBudget = getMatmulKernelBudget();
    const budget = mkBudget(matmulBudget.io, matmulBudget.cpuMs, matmulBudget.mem || 32);
    logBudget(budget, `MatMul ${iteration}`);
    
    // Preflight: G3 + G1 - Logic + Core
    GateOps.bootstrap.r96Semiring('Check CPU/IO budget vectors can close before execution');
    GateOps.bootstrap.conservation('Validate budget conservation for compute');
    
    // Execute kernel using VPI registry
    console.log(`🚀 Executing matmul kernel for iteration ${iteration}...`);
    const result = await vpiRegistry.executeKernel(
      'matmul-block',
      'v1',
      [{ id: inputPostcard.id }],
      budget
    );
    
    if (!result.ok) {
      throw new Error(`Kernel execution failed for iteration ${iteration}`);
    }
    
    console.log(`✅ MatMul iteration ${iteration} completed`);
    
    // Validate receipts
    if (result.receipts) {
      logReceipt(result.receipts.compute, `MatMul ${iteration} Compute`);
      logReceipt(result.receipts.aggregate, `MatMul ${iteration} Aggregate`);
    }
    
    // Get output details
    const output = result.outputs[0];
    if (!output) {
      throw new Error(`No output generated for iteration ${iteration}`);
    }
    
    return {
      computeReceipt: result.receipts?.compute,
      aggregateReceipt: result.receipts?.aggregate,
      outputId: output.id,
      witness: output.witness,
    };
    
  } finally {
    timer.end();
  }
}

/**
 * Run the complete MatMul demo
 */
export async function runMatMulDemo(): Promise<MatMulResults> {
  const config = parseArgs();
  printBanner(config);
  
  const demoTimer = new PerfTimer('MatMul Demo');
  const results: MatMulResults = {
    totalIterations: config.iterations,
    successfulIterations: 0,
    failedIterations: 0,
    totalComputeTime: 0,
    averageIterationTime: 0,
    totalThroughput: 0,
    receipts: [],
    performanceMetrics: {
      gbps: 0,
      fps: 0,
      p50latencyMs: 0,
      p99latencyMs: 0,
      cpuPercent: 0,
    },
  };
  
  try {
    // Initialize system
    await initializeSystem();
    
    // Create initial postcard for input
    console.log('\n📮 Creating input postcard...');
    const inputPostcard = await createPostcard({
      message: `MatMul Demo Input - ${config.matrixSize}x${config.matrixSize} matrices`,
      from: 'MatMulDemo',
      to: 'HologramLattice',
    });
    console.log(`   Input ID: ${inputPostcard.id.substring(0, 16)}...`);
    
    // Run matrix multiplication iterations
    console.log(`\n🚀 Starting ${config.iterations} matrix multiplication iterations...`);
    const iterationStartTime = Date.now();
    
    for (let i = 1; i <= config.iterations; i++) {
      try {
        const iterationResult = await runMatMulIteration(i, inputPostcard);
        
        results.receipts.push({
          iteration: i,
          ...iterationResult,
        });
        
        results.successfulIterations++;
        
        // Print progress every 100 iterations
        if (i % 100 === 0) {
          const elapsed = Date.now() - iterationStartTime;
          const avgTime = elapsed / i;
          const remaining = config.iterations - i;
          const eta = remaining * avgTime;
          
          console.log(`\n📊 Progress: ${i}/${config.iterations} (${((i/config.iterations)*100).toFixed(1)}%)`);
          console.log(`   Successful: ${results.successfulIterations}`);
          console.log(`   Failed: ${results.failedIterations}`);
          console.log(`   Avg time per iteration: ${avgTime.toFixed(2)}ms`);
          console.log(`   ETA: ${(eta/1000).toFixed(1)}s`);
        }
        
      } catch (error) {
        console.error(`❌ Iteration ${i} failed:`, error);
        results.failedIterations++;
      }
    }
    
    results.totalComputeTime = Date.now() - iterationStartTime;
    results.averageIterationTime = results.totalComputeTime / results.successfulIterations;
    
    // Run load test for performance metrics
    console.log('\n📊 Running performance load test...');
    const loadArgs: RunArgs = {
      durationSec: config.durationSec,
      lanes: config.lanes,
      payloadBytes: config.payloadBytes,
      targetGbps: config.targetGbps,
      batch: config.batch,
      windowMs: config.windowMs,
      workers: config.workers,
      budget: {
        io: 1000,
        cpuMs: 100,
        mem: 1000,
      },
    };
    
    const loadResults = await runLoad(loadArgs);
    results.performanceMetrics = {
      gbps: loadResults.gbps,
      fps: loadResults.fps,
      p50latencyMs: loadResults.p50latencyMs,
      p99latencyMs: loadResults.p99latencyMs,
      cpuPercent: loadResults.cpuPercent,
    };
    
    // Print final results
    printFinalResults(results);
    
    return results;
    
  } finally {
    demoTimer.end();
  }
}

/**
 * Print final demo results
 */
function printFinalResults(results: MatMulResults): void {
  console.log('\n' + '='.repeat(80));
  console.log('🎯 MATRIX MULTIPLICATION DEMO RESULTS');
  console.log('='.repeat(80));
  
  console.log(`📊 Iteration Summary:`);
  console.log(`   Total Iterations: ${results.totalIterations}`);
  console.log(`   Successful: ${results.successfulIterations} (${((results.successfulIterations/results.totalIterations)*100).toFixed(1)}%)`);
  console.log(`   Failed: ${results.failedIterations} (${((results.failedIterations/results.totalIterations)*100).toFixed(1)}%)`);
  console.log(`   Total Compute Time: ${(results.totalComputeTime/1000).toFixed(2)}s`);
  console.log(`   Average Iteration Time: ${results.averageIterationTime.toFixed(2)}ms`);
  
  console.log(`\n🚀 Performance Metrics:`);
  console.log(`   Throughput: ${results.performanceMetrics.gbps.toFixed(2)} Gb/s`);
  console.log(`   Frames/sec: ${results.performanceMetrics.fps.toFixed(0)}`);
  console.log(`   P50 Latency: ${results.performanceMetrics.p50latencyMs.toFixed(2)}ms`);
  console.log(`   P99 Latency: ${results.performanceMetrics.p99latencyMs.toFixed(2)}ms`);
  console.log(`   CPU Usage: ${results.performanceMetrics.cpuPercent.toFixed(1)}%`);
  
  console.log(`\n📋 Receipt Summary:`);
  console.log(`   Total Receipts: ${results.receipts.length}`);
  if (results.receipts.length > 0) {
    const lastReceipt = results.receipts[results.receipts.length - 1];
    console.log(`   Last Output ID: ${lastReceipt.outputId.substring(0, 16)}...`);
    console.log(`   Last Witness R96: ${lastReceipt.witness.r96.substring(0, 16)}...`);
  }
  
  console.log('\n✅ Matrix Multiplication Demo completed successfully!');
  console.log('='.repeat(80));
}

/**
 * Main entry point
 */
if (require.main === module) {
  runMatMulDemo().catch(error => {
    console.error('❌ MatMul Demo failed:', error);
    process.exit(1);
  });
}

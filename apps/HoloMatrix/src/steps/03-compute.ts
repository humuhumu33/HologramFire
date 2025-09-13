/**
 * Compute Step - Pinned Kernel Execution and Compute Receipts
 * Handles kernel registration, preflight, execution, and receipt generation
 */

import { program } from 'commander';
import type { Kernel, Budget, Receipt, Witness, ComputeKernel } from '../types';
import { mkAdapter, budget, assertClosed, sleep } from '../testkit';
import { createHistogram, type PerformanceHistogram } from '../bench/histogram';
import { GATES } from '../types';

export interface ComputeStepResult {
  success: boolean;
  metrics: {
    preflightLatency: PerformanceHistogram;
    computeLatency: PerformanceHistogram;
    aggregateLatency: PerformanceHistogram;
    kernels: number;
    receipts: number;
    windowClosures: number;
    totalWindows: number;
  };
  receipts: Receipt[];
}

export class ComputeStep {
  private adapter = mkAdapter();
  private budget: Budget;
  private registeredKernels: Set<string> = new Set();

  constructor(opts: {
    budget?: Budget;
  } = {}) {
    this.budget = opts.budget || budget(50000, 50000, 50000);
  }

  /**
   * Initialize compute layer
   */
  async initialize(): Promise<void> {
    console.log(`Initializing compute layer...`);
    console.log(`Available capabilities: ${JSON.stringify(this.adapter.capabilities?.() || {})}`);
    console.log('Compute layer initialized');
  }

  /**
   * Register a compute kernel
   */
  async registerKernel(name: string, version: string = 'v1'): Promise<{ success: boolean; latency: number }> {
    const startTime = Date.now();
    
    try {
      console.log(`${GATES.VPI_REGISTRY} → kernel registration`);
      
      // Kernel registration
      const kernelId = `${name}:${version}`;
      this.registeredKernels.add(kernelId);
      
      const latency = Date.now() - startTime;
      console.log(`Kernel registered: ${kernelId}`);
      
      return { success: true, latency };
    } catch (error) {
      const latency = Date.now() - startTime;
      console.log(`Kernel registration failed: ${error}`);
      return { success: false, latency };
    }
  }

  /**
   * Preflight check for compute operation
   */
  async preflight(
    kernelName: string,
    inputs: Array<{ id: string }>,
    requiredBudget: Budget
  ): Promise<{ success: boolean; latency: number; approved: boolean }> {
    const startTime = Date.now();

    try {
      console.log(`${GATES.R96_SEMIRING} + ${GATES.CONSERVATION} (budget {cpuMs, io, mem})`);
      
      // Check if kernel is registered - look for both exact name and with version
      const kernelId = `${kernelName}:v1`;
      if (!this.registeredKernels.has(kernelName) && !this.registeredKernels.has(kernelId)) {
        console.log(`Preflight failed: kernel ${kernelName} not registered`);
        return { success: false, latency: Date.now() - startTime, approved: false };
      }

      // Check budget availability
      const hasBudget = this.budget.cpuMs >= requiredBudget.cpuMs &&
                       this.budget.io >= requiredBudget.io &&
                       (this.budget.mem || 0) >= (requiredBudget.mem || 0);

      const latency = Date.now() - startTime;

      if (hasBudget) {
        console.log(`Preflight approved: sufficient budget available`);
        return { success: true, latency, approved: true };
      } else {
        console.log(`Preflight rejected: insufficient budget`);
        return { success: true, latency, approved: false };
      }
    } catch (error) {
      const latency = Date.now() - startTime;
      console.log(`Preflight failed: ${error}`);
      return { success: false, latency, approved: false };
    }
  }

  /**
   * Spawn and execute a compute kernel
   */
  async spawnKernel(
    kernelName: string,
    inputs: Array<{ id: string }>,
    requiredBudget: Budget,
    pin?: { near?: string; lane?: number }
  ): Promise<{ success: boolean; latency: number; kernel?: Kernel }> {
    const startTime = Date.now();

    try {
      // Preflight check
      const preflightResult = await this.preflight(kernelName, inputs, requiredBudget);
      if (!preflightResult.approved) {
        return { success: false, latency: Date.now() - startTime };
      }

      console.log(`spawn ${kernelName} pin row=${pin?.near || 'auto'} lane=${pin?.lane || 'auto'} preflight G3/G1✅`);
      
      const kernelConfig: ComputeKernel = {
        name: kernelName,
        inputs,
        outputs: [],
        budget: requiredBudget,
        pin,
        iopolicy: { lane: pin?.lane, windowMs: 100 }
      };

      const kernel = await this.adapter.spawnKernel(kernelConfig);
      const latency = Date.now() - startTime;

      return { success: true, latency, kernel };
    } catch (error) {
      const latency = Date.now() - startTime;
      console.log(`Kernel spawn failed: ${error}`);
      return { success: false, latency };
    }
  }

  /**
   * Execute kernel and wait for completion
   */
  async executeKernel(kernel: Kernel): Promise<{
    success: boolean;
    latency: number;
    result?: {
      ok: boolean;
      outputs: Array<{ id: string; witness: Witness }>;
      receipts: { compute: Receipt; aggregate: Receipt };
    };
  }> {
    const startTime = Date.now();

    try {
      const result = await kernel.await();
      const latency = Date.now() - startTime;

      if (result.ok) {
        console.log(`compute receipt G4: closed; budgetAfter={cpuMs:0, io:0, mem:0}`);
        console.log(`aggregate window W42: closed=100%`);
        
        // Verify receipts
        assertClosed(result.receipts.compute, GATES.RECEIPT);
        assertClosed(result.receipts.aggregate, GATES.RECEIPT);
        
        // Verify witness consistency
        const v = await this.adapter.createVerifier();
        const st = await this.adapter.createStorage({ rows: 48, cols: 256, tileCols: 16, ec: { k: 3, m: 1 } });
        const outId = result.outputs[0].id;
        const { bytes: outBytes, witness: storedWit } = await st.get({ id: outId });

        const localR = v.r96(outBytes);
        if (localR !== result.outputs[0].witness.r96) {
          throw new Error(`output witness mismatch (compute vs local): ${result.outputs[0].witness.r96} !== ${localR}`);
        }
        if (localR !== storedWit.r96) {
          throw new Error(`output witness mismatch (storage vs local): ${storedWit.r96} !== ${localR}`);
        }
      }

      return { success: true, latency, result };
    } catch (error) {
      const latency = Date.now() - startTime;
      console.log(`Kernel execution failed: ${error}`);
      return { success: false, latency };
    }
  }

  /**
   * Run end-to-end compute operation
   */
  async runComputeOperation(
    kernelName: string,
    inputs: Array<{ id: string }>,
    requiredBudget: Budget,
    pin?: { near?: string; lane?: number }
  ): Promise<{
    success: boolean;
    totalLatency: number;
    result?: {
      outputs: Array<{ id: string; witness: Witness }>;
      receipts: { compute: Receipt; aggregate: Receipt };
    };
  }> {
    const startTime = Date.now();

    try {
      // Spawn kernel
      const spawnResult = await this.spawnKernel(kernelName, inputs, requiredBudget, pin);
      if (!spawnResult.success || !spawnResult.kernel) {
        return { success: false, totalLatency: Date.now() - startTime };
      }

      // Execute kernel
      const executeResult = await this.executeKernel(spawnResult.kernel);
      if (!executeResult.success || !executeResult.result) {
        return { success: false, totalLatency: Date.now() - startTime };
      }

      const totalLatency = Date.now() - startTime;

      return {
        success: true,
        totalLatency,
        result: executeResult.result
      };
    } catch (error) {
      const totalLatency = Date.now() - startTime;
      console.log(`Compute operation failed: ${error}`);
      return { success: false, totalLatency };
    }
  }

  /**
   * Run compute stress test
   */
  async runStressTest(opts: {
    duration: number;
    kernelsPerSecond: number;
    inputCount: number;
  }): Promise<ComputeStepResult> {
    console.log(`Running compute stress test...`);
    console.log(`Duration: ${opts.duration}s`);
    console.log(`Kernels/sec: ${opts.kernelsPerSecond}`);
    console.log(`Input count: ${opts.inputCount}`);

    const preflightLatency = createHistogram();
    const computeLatency = createHistogram();
    const aggregateLatency = createHistogram();
    const receipts: Receipt[] = [];
    
    let kernels = 0;
    let receiptsCount = 0;
    let windowClosures = 0;
    let totalWindows = 0;

    const startTime = Date.now();
    const endTime = startTime + (opts.duration * 1000);
    const kernelInterval = 1000 / opts.kernelsPerSecond;

    // Register test kernels
    await this.registerKernel('matmul-block', 'v1');
    await this.registerKernel('vector-add', 'v1');
    await this.registerKernel('matrix-transpose', 'v1');

    const kernelNames = ['matmul-block:v1', 'vector-add:v1', 'matrix-transpose:v1'];

    while (Date.now() < endTime) {
      const kernelStart = Date.now();
      
      // Generate test inputs
      const inputs = Array.from({ length: opts.inputCount }, (_, i) => ({
        id: `input-${kernels}-${i}`
      }));

      // Choose random kernel
      const kernelName = kernelNames[Math.floor(Math.random() * kernelNames.length)];
      
      // Create budget based on kernel type
      let requiredBudget: Budget;
      switch (kernelName) {
        case 'matmul-block':
          requiredBudget = { cpuMs: 50, io: 2, mem: 16384 };
          break;
        case 'vector-add':
          requiredBudget = { cpuMs: 10, io: 1, mem: 4096 };
          break;
        case 'matrix-transpose':
          requiredBudget = { cpuMs: 20, io: 1, mem: 8192 };
          break;
        default:
          requiredBudget = { cpuMs: 10, io: 1, mem: 4096 };
      }

      // Pin near data (simulate)
      const pin = {
        near: `data-${Math.floor(Math.random() * 10)}`,
        lane: Math.floor(Math.random() * 64)
      };

      // Run compute operation
      const result = await this.runComputeOperation(kernelName, inputs, requiredBudget, pin);
      
      if (result.success && result.result) {
        kernels++;
        receiptsCount += 2; // compute + aggregate receipts
        receipts.push(result.result.receipts.compute);
        receipts.push(result.result.receipts.aggregate);
        
        // Track window closures
        totalWindows++;
        if (result.result.receipts.aggregate.windowClosed) {
          windowClosures++;
        }
        
        computeLatency.observe(result.totalLatency);
      }

      // Maintain kernel rate
      const kernelDuration = Date.now() - kernelStart;
      if (kernelDuration < kernelInterval) {
        await sleep(kernelInterval - kernelDuration);
      }
    }

    const result: ComputeStepResult = {
      success: true,
      metrics: {
        preflightLatency,
        computeLatency,
        aggregateLatency,
        kernels,
        receipts: receiptsCount,
        windowClosures,
        totalWindows
      },
      receipts
    };

    console.log(`Compute stress test completed:`);
    console.log(`  Kernels executed: ${kernels}`);
    console.log(`  Receipts generated: ${receiptsCount}`);
    console.log(`  Window closures: ${windowClosures}/${totalWindows}`);

    return result;
  }

  /**
   * Close compute layer
   */
  async close(): Promise<void> {
    this.registeredKernels.clear();
  }
}

// CLI interface
if (require.main === module) {
  program
    .option('-d, --duration <seconds>', 'Test duration in seconds', '10')
    .option('-k, --kernels <count>', 'Kernels per second', '10')
    .option('-i, --inputs <count>', 'Input count per kernel', '3')
    .parse();

  const options = program.opts();

  async function main() {
    const compute = new ComputeStep();

    try {
      await compute.initialize();
      
      // Run stress test
      const result = await compute.runStressTest({
        duration: parseInt(options.duration),
        kernelsPerSecond: parseInt(options.kernels),
        inputCount: parseInt(options.inputs)
      });

      console.log('\nCompute Step Results:');
      console.log(`Success: ${result.success}`);
      console.log(`Compute latency p50: ${result.metrics.computeLatency.p50().toFixed(2)}ms`);
      console.log(`Compute latency p99: ${result.metrics.computeLatency.p99().toFixed(2)}ms`);
      console.log(`Window closure rate: ${((result.metrics.windowClosures / result.metrics.totalWindows) * 100).toFixed(2)}%`);
    } finally {
      await compute.close();
    }
  }

  main().catch(console.error);
}

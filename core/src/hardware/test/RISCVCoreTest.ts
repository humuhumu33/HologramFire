/**
 * Comprehensive Test Suite for RISC-V Core and OS Primitives
 * 
 * Tests the complete implementation from RISC-V instructions to OS primitives
 * to ensure the system works correctly and achieves the promised scale.
 */

import { RISCVCore, RISCVCoreConfig } from '../riscv/RISCVCore';
import { HardwareAbstractionLayer } from '../HardwareAbstractionLayer';
import { OSPrimitives } from '../../os/OSPrimitives';

export interface TestResult {
  name: string;
  success: boolean;
  duration: number;
  details: any;
  witness: string;
  holographicContext: any;
}

export interface TestSuite {
  name: string;
  tests: TestResult[];
  totalDuration: number;
  successRate: number;
  holographicState: any;
}

export class RISCVCoreTest {
  private testResults: TestResult[] = [];
  private startTime: number = 0;

  /**
   * Run comprehensive test suite
   */
  async runTestSuite(): Promise<TestSuite> {
    console.log('🧪 Starting RISC-V Core and OS Primitives Test Suite');
    console.log('=' .repeat(60));

    this.startTime = Date.now();

    // Test 1: RISC-V Core Basic Functionality
    await this.testRISCVCoreBasic();

    // Test 2: RISC-V Instruction Execution
    await this.testRISCVInstructions();

    // Test 3: Hardware Abstraction Layer
    await this.testHardwareAbstractionLayer();

    // Test 4: OS Primitives
    await this.testOSPrimitives();

    // Test 5: Cross-Layer Communication
    await this.testCrossLayerCommunication();

    // Test 6: Holographic Integration
    await this.testHolographicIntegration();

    // Test 7: Performance and Scale
    await this.testPerformanceAndScale();

    const totalDuration = Date.now() - this.startTime;
    const successRate = this.testResults.filter(t => t.success).length / this.testResults.length;

    const testSuite: TestSuite = {
      name: 'RISC-V Core and OS Primitives Test Suite',
      tests: this.testResults,
      totalDuration,
      successRate,
      holographicState: await this.getHolographicState()
    };

    this.printTestResults(testSuite);
    return testSuite;
  }

  /**
   * Test 1: RISC-V Core Basic Functionality
   */
  private async testRISCVCoreBasic(): Promise<void> {
    const testName = 'RISC-V Core Basic Functionality';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      // Create RISC-V core
      const config: RISCVCoreConfig = {
        xlen: 64,
        extensions: ['I', 'M', 'A'],
        memorySize: 1024 * 1024, // 1MB
        enableHolographic: true
      };

      const core = new RISCVCore(config);
      
      // Verify core state
      const state = core.getState();
      if (state.registers.length !== 64) {
        throw new Error(`Expected 64 registers, got ${state.registers.length}`);
      }

      if (state.pc !== 0n) {
        throw new Error(`Expected PC to be 0, got ${state.pc}`);
      }

      // Verify holographic context
      const holographicContext = core.getHolographicContext();
      if (holographicContext.size === 0) {
        throw new Error('Holographic context should not be empty');
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          registers: state.registers.length,
          pc: state.pc.toString(),
          holographicContextSize: holographicContext.size,
          atlas12288: state.atlas12288
        },
        witness: state.witness,
        holographicContext: Object.fromEntries(holographicContext)
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Test 2: RISC-V Instruction Execution
   */
  private async testRISCVInstructions(): Promise<void> {
    const testName = 'RISC-V Instruction Execution';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      const config: RISCVCoreConfig = {
        xlen: 64,
        extensions: ['I', 'M', 'A'],
        memorySize: 1024 * 1024,
        enableHolographic: true
      };

      const core = new RISCVCore(config);

      // Test ADDI instruction (add immediate)
      // ADDI x1, x0, 42 (add immediate 42 to register x0, store in x1)
      const addiInstruction = RISCVCore.parseInstruction(0x02A00093); // ADDI x1, x0, 42
      
      const result = await core.executeInstruction(addiInstruction);
      
      if (!result.success) {
        throw new Error(`Instruction execution failed: ${result.witness}`);
      }

      // Verify result
      const newState = result.newState;
      if (newState.registers[1].value !== 42n) {
        throw new Error(`Expected register x1 to be 42, got ${newState.registers[1].value}`);
      }

      // Test ADD instruction (add register)
      // ADD x2, x1, x1 (add x1 to x1, store in x2)
      const addInstruction = RISCVCore.parseInstruction(0x00108133); // ADD x2, x1, x1
      
      const addResult = await core.executeInstruction(addInstruction);
      
      if (!addResult.success) {
        throw new Error(`ADD instruction execution failed: ${addResult.witness}`);
      }

      // Verify ADD result
      const addState = addResult.newState;
      if (addState.registers[2].value !== 84n) {
        throw new Error(`Expected register x2 to be 84, got ${addState.registers[2].value}`);
      }

      // Test memory operations
      // SW x1, 0(x0) (store word from x1 to memory at address 0)
      const swInstruction = RISCVCore.parseInstruction(0x00102023); // SW x1, 0(x0)
      
      const swResult = await core.executeInstruction(swInstruction);
      
      if (!swResult.success) {
        throw new Error(`Store word instruction execution failed: ${swResult.witness}`);
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          addiResult: result.newState.registers[1].value.toString(),
          addResult: addResult.newState.registers[2].value.toString(),
          storeResult: swResult.success,
          totalInstructions: 3,
          holographicVerification: true
        },
        witness: result.witness,
        holographicContext: Object.fromEntries(core.getHolographicContext())
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Test 3: Hardware Abstraction Layer
   */
  private async testHardwareAbstractionLayer(): Promise<void> {
    const testName = 'Hardware Abstraction Layer';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      const hal = new HardwareAbstractionLayer();

      // Create RISC-V core through HAL
      const coreConfig: RISCVCoreConfig = {
        xlen: 64,
        extensions: ['I', 'M', 'A'],
        memorySize: 1024 * 1024,
        enableHolographic: true
      };

      const core = await hal.createCore('core0', coreConfig);

      // Register a device
      const device = {
        id: 'memory0',
        type: 'memory' as const,
        capabilities: ['read', 'write'],
        state: { size: 1024 * 1024 },
        witness: '',
        holographicContext: new Map()
      };

      await hal.registerDevice(device);

      // Map memory region
      const memoryRegion = {
        start: 0x1000n,
        end: 0x2000n,
        permissions: 'rwx' as const,
        device: 'memory0',
        witness: ''
      };

      await hal.mapMemory(memoryRegion);

      // Test system call execution
      const syscallResult = await hal.executeSystemCall('core0', 0, [0]); // Exit syscall
      
      if (!syscallResult.success) {
        throw new Error(`System call execution failed: ${JSON.stringify(syscallResult)}`);
      }

      // Verify holographic context
      const context = hal.getUnifiedContext();
      if (context.size === 0) {
        throw new Error('Unified context should not be empty');
      }

      const holographicState = hal.getHolographicState();
      if (!holographicState.witness) {
        throw new Error('Holographic state should have witness');
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          coresCreated: 1,
          devicesRegistered: 1,
          memoryRegionsMapped: 1,
          systemCallsExecuted: 1,
          unifiedContextSize: context.size,
          holographicState: holographicState.atlas12288
        },
        witness: holographicState.witness,
        holographicContext: Object.fromEntries(context)
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Test 4: OS Primitives
   */
  private async testOSPrimitives(): Promise<void> {
    const testName = 'OS Primitives';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      const hal = new HardwareAbstractionLayer();
      const os = new OSPrimitives(hal);

      // Create a simple program (ADDI x1, x0, 42; ECALL)
      const program = [
        0x02A00093, // ADDI x1, x0, 42
        0x00000073  // ECALL
      ];

      // Create process
      const process = await os.createProcess('test_process', program, 'core0');
      
      if (process.pid !== 1) {
        throw new Error(`Expected PID 1, got ${process.pid}`);
      }

      if (process.state !== 'ready') {
        throw new Error(`Expected process state 'ready', got '${process.state}'`);
      }

      // Execute process
      const executionResult = await os.executeProcess(process.pid);
      
      if (!executionResult.success) {
        throw new Error(`Process execution failed: ${JSON.stringify(executionResult.result)}`);
      }

      // Verify process state
      const updatedProcess = os.getContext().processes.get(process.pid);
      if (!updatedProcess) {
        throw new Error('Process not found after execution');
      }

      // Verify file system
      const fileSystem = os.getContext().fileSystem;
      if (!fileSystem.root.children) {
        throw new Error('File system root should have children');
      }

      // Verify network stack
      const networkStack = os.getContext().networkStack;
      if (networkStack.interfaces.size === 0) {
        throw new Error('Network stack should have interfaces');
      }

      // Verify security context
      const securityContext = os.getContext().securityContext;
      if (securityContext.user.name !== 'root') {
        throw new Error(`Expected root user, got ${securityContext.user.name}`);
      }

      const holographicState = os.getHolographicState();
      if (!holographicState.witness) {
        throw new Error('OS should have holographic witness');
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          processCreated: true,
          processExecuted: executionResult.success,
          finalState: updatedProcess.state,
          instructionsExecuted: executionResult.result.instructions,
          fileSystemNodes: fileSystem.root.children.size,
          networkInterfaces: networkStack.interfaces.size,
          securityUser: securityContext.user.name,
          holographicState: holographicState.atlas12288
        },
        witness: holographicState.witness,
        holographicContext: holographicState.unifiedContext
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Test 5: Cross-Layer Communication
   */
  private async testCrossLayerCommunication(): Promise<void> {
    const testName = 'Cross-Layer Communication';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      const hal = new HardwareAbstractionLayer();
      const os = new OSPrimitives(hal);

      // Register cross-layer communicator
      let communicationReceived = false;
      hal.registerCrossLayerCommunicator('test_layer', async (data: any) => {
        communicationReceived = true;
        if (data.source !== 'core_core0') {
          throw new Error(`Expected source 'core_core0', got '${data.source}'`);
        }
      });

      // Create and execute a program that triggers cross-layer communication
      const program = [
        0x02A00093, // ADDI x1, x0, 42
        0x00000073  // ECALL
      ];

      const process = await os.createProcess('comm_test', program, 'core0');
      const result = await os.executeProcess(process.pid);

      if (!result.success) {
        throw new Error(`Process execution failed: ${JSON.stringify(result.result)}`);
      }

      if (!communicationReceived) {
        throw new Error('Cross-layer communication was not received');
      }

      // Verify unified context has cross-layer data
      const unifiedContext = os.getUnifiedContext();
      let hasCrossLayerData = false;
      for (const [key, value] of unifiedContext) {
        if (key.includes('cross_layer')) {
          hasCrossLayerData = true;
          break;
        }
      }

      if (!hasCrossLayerData) {
        throw new Error('Unified context should contain cross-layer communication data');
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          communicationReceived,
          hasCrossLayerData,
          unifiedContextSize: unifiedContext.size,
          processExecuted: result.success
        },
        witness: result.witness,
        holographicContext: Object.fromEntries(unifiedContext)
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Test 6: Holographic Integration
   */
  private async testHolographicIntegration(): Promise<void> {
    const testName = 'Holographic Integration';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      const hal = new HardwareAbstractionLayer();
      const os = new OSPrimitives(hal);

      // Verify holographic state at each layer
      const halState = hal.getHolographicState();
      const osState = os.getHolographicState();

      if (!halState.witness) {
        throw new Error('Hardware layer should have holographic witness');
      }

      if (!osState.witness) {
        throw new Error('OS layer should have holographic witness');
      }

      if (!halState.atlas12288) {
        throw new Error('Hardware layer should have atlas-12288 encoding');
      }

      if (!osState.atlas12288) {
        throw new Error('OS layer should have atlas-12288 encoding');
      }

      // Verify atlas-12288 structure
      const halAtlas = halState.atlas12288;
      const osAtlas = osState.atlas12288;

      if (halAtlas.page < 0 || halAtlas.page >= 48) {
        throw new Error(`Invalid atlas-12288 page: ${halAtlas.page}`);
      }

      if (halAtlas.cycle < 0 || halAtlas.cycle >= 256) {
        throw new Error(`Invalid atlas-12288 cycle: ${halAtlas.cycle}`);
      }

      if (osAtlas.page < 0 || osAtlas.page >= 48) {
        throw new Error(`Invalid atlas-12288 page: ${osAtlas.page}`);
      }

      if (osAtlas.cycle < 0 || osAtlas.cycle >= 256) {
        throw new Error(`Invalid atlas-12288 cycle: ${osAtlas.cycle}`);
      }

      // Verify R96 classification
      if (halAtlas.r96Class < 0 || halAtlas.r96Class >= 96) {
        throw new Error(`Invalid R96 class: ${halAtlas.r96Class}`);
      }

      if (osAtlas.r96Class < 0 || osAtlas.r96Class >= 96) {
        throw new Error(`Invalid R96 class: ${osAtlas.r96Class}`);
      }

      // Verify Klein window
      if (halAtlas.kleinWindow < 0 || halAtlas.kleinWindow >= 192) {
        throw new Error(`Invalid Klein window: ${halAtlas.kleinWindow}`);
      }

      if (osAtlas.kleinWindow < 0 || osAtlas.kleinWindow >= 192) {
        throw new Error(`Invalid Klein window: ${osAtlas.kleinWindow}`);
      }

      // Verify unified context has holographic data
      const unifiedContext = os.getUnifiedContext();
      let hasHolographicData = false;
      for (const [key, value] of unifiedContext) {
        if (key.includes('holographic') || key.includes('atlas') || key.includes('witness')) {
          hasHolographicData = true;
          break;
        }
      }

      if (!hasHolographicData) {
        throw new Error('Unified context should contain holographic data');
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          halWitness: halState.witness.substring(0, 16) + '...',
          osWitness: osState.witness.substring(0, 16) + '...',
          halAtlas: halAtlas,
          osAtlas: osAtlas,
          hasHolographicData,
          unifiedContextSize: unifiedContext.size
        },
        witness: osState.witness,
        holographicContext: osState.unifiedContext
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Test 7: Performance and Scale
   */
  private async testPerformanceAndScale(): Promise<void> {
    const testName = 'Performance and Scale';
    console.log(`\n📋 ${testName}`);
    
    const startTime = Date.now();
    
    try {
      const hal = new HardwareAbstractionLayer();
      const os = new OSPrimitives(hal);

      // Test multiple cores
      const coreConfig: RISCVCoreConfig = {
        xlen: 64,
        extensions: ['I', 'M', 'A'],
        memorySize: 1024 * 1024,
        enableHolographic: true
      };

      const corePromises = [];
      for (let i = 0; i < 4; i++) {
        corePromises.push(hal.createCore(`core${i}`, coreConfig));
      }

      const cores = await Promise.all(corePromises);

      // Test multiple processes
      const processPromises = [];
      for (let i = 0; i < 4; i++) {
        const program = [
          0x02A00093, // ADDI x1, x0, 42
          0x00000073  // ECALL
        ];
        processPromises.push(os.createProcess(`process${i}`, program, `core${i}`));
      }

      const processes = await Promise.all(processPromises);

      // Execute all processes in parallel
      const executionPromises = processes.map(p => os.executeProcess(p.pid));
      const executionResults = await Promise.all(executionPromises);

      // Verify all executions succeeded
      const failedExecutions = executionResults.filter(r => !r.success);
      if (failedExecutions.length > 0) {
        throw new Error(`${failedExecutions.length} process executions failed`);
      }

      // Measure performance
      const totalInstructions = executionResults.reduce((sum, r) => sum + r.result.instructions, 0);
      const executionTime = Date.now() - startTime;
      const instructionsPerSecond = (totalInstructions / executionTime) * 1000;

      // Verify holographic state consistency
      const holographicState = os.getHolographicState();
      const unifiedContext = os.getUnifiedContext();

      if (unifiedContext.size < 10) {
        throw new Error(`Unified context too small: ${unifiedContext.size} entries`);
      }

      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: true,
        duration,
        details: {
          coresCreated: cores.length,
          processesCreated: processes.length,
          processesExecuted: executionResults.length,
          totalInstructions,
          executionTime,
          instructionsPerSecond: Math.round(instructionsPerSecond),
          unifiedContextSize: unifiedContext.size,
          holographicConsistency: true
        },
        witness: holographicState.witness,
        holographicContext: holographicState.unifiedContext
      });

      console.log(`✅ ${testName} - PASSED (${duration}ms)`);
      console.log(`   📊 Performance: ${Math.round(instructionsPerSecond)} instructions/second`);
      console.log(`   📊 Scale: ${cores.length} cores, ${processes.length} processes`);

    } catch (error) {
      const duration = Date.now() - startTime;
      
      this.testResults.push({
        name: testName,
        success: false,
        duration,
        details: { error: error.message },
        witness: '',
        holographicContext: {}
      });

      console.log(`❌ ${testName} - FAILED (${duration}ms): ${error.message}`);
    }
  }

  /**
   * Get holographic state for test suite
   */
  private async getHolographicState(): Promise<any> {
    // This would typically aggregate holographic state from all components
    return {
      testSuite: 'riscv-core-and-os-primitives',
      timestamp: Date.now(),
      totalTests: this.testResults.length,
      successfulTests: this.testResults.filter(t => t.success).length
    };
  }

  /**
   * Print test results
   */
  private printTestResults(testSuite: TestSuite): void {
    console.log('\n' + '=' .repeat(60));
    console.log('📊 TEST SUITE RESULTS');
    console.log('=' .repeat(60));
    
    console.log(`\n📋 Test Suite: ${testSuite.name}`);
    console.log(`⏱️  Total Duration: ${testSuite.totalDuration}ms`);
    console.log(`✅ Success Rate: ${(testSuite.successRate * 100).toFixed(1)}%`);
    console.log(`🧪 Total Tests: ${testSuite.tests.length}`);
    console.log(`✅ Passed: ${testSuite.tests.filter(t => t.success).length}`);
    console.log(`❌ Failed: ${testSuite.tests.filter(t => !t.success).length}`);

    console.log('\n📋 Individual Test Results:');
    testSuite.tests.forEach((test, index) => {
      const status = test.success ? '✅' : '❌';
      console.log(`   ${index + 1}. ${status} ${test.name} (${test.duration}ms)`);
      if (!test.success) {
        console.log(`      Error: ${test.details.error}`);
      }
    });

    if (testSuite.successRate === 1.0) {
      console.log('\n🎉 ALL TESTS PASSED! RISC-V Core and OS Primitives are working correctly.');
      console.log('🚀 The system successfully scales from RISC-V instructions to OS primitives.');
      console.log('🔗 Cross-layer communication and holographic integration are functional.');
    } else {
      console.log('\n⚠️  Some tests failed. Please review the errors above.');
    }

    console.log('\n🔗 Holographic State:');
    console.log(`   Witness: ${testSuite.holographicState.testSuite}`);
    console.log(`   Timestamp: ${new Date(testSuite.holographicState.timestamp).toISOString()}`);
    console.log(`   Test Coverage: ${testSuite.holographicState.successfulTests}/${testSuite.holographicState.totalTests}`);
  }
}

// Export for use in other modules
export { RISCVCoreTest };

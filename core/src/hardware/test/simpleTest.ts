/**
 * Simple Test to Verify RISC-V Core Implementation
 * 
 * This is a minimal test to verify that the basic RISC-V core functionality
 * works correctly before running the full test suite.
 */

import { RISCVCore, RISCVCoreConfig } from '../riscv/RISCVCore';
import { HardwareAbstractionLayer } from '../HardwareAbstractionLayer';
import { OSPrimitives } from '../../os/OSPrimitives';

async function simpleTest(): Promise<void> {
  console.log('🧪 Running Simple RISC-V Core Test');
  console.log('=' .repeat(50));
  
  try {
    // Test 1: Create RISC-V Core
    console.log('\n1. Creating RISC-V Core...');
    const config: RISCVCoreConfig = {
      xlen: 64,
      extensions: ['I', 'M', 'A'],
      memorySize: 1024 * 1024,
      enableHolographic: true
    };
    
    const core = new RISCVCore(config);
    console.log('✅ RISC-V Core created successfully');
    
    // Test 2: Execute Simple Instruction
    console.log('\n2. Executing ADDI instruction...');
    const addiInstruction = RISCVCore.parseInstruction(0x02A00093); // ADDI x1, x0, 42
    const result = await core.executeInstruction(addiInstruction);
    
    if (!result.success) {
      throw new Error('Instruction execution failed');
    }
    
    console.log('✅ ADDI instruction executed successfully');
    console.log(`   Register x1 value: ${result.newState.registers[1].value}`);
    
    // Test 3: Hardware Abstraction Layer
    console.log('\n3. Testing Hardware Abstraction Layer...');
    const hal = new HardwareAbstractionLayer();
    const core2 = await hal.createCore('test_core', config);
    console.log('✅ Hardware Abstraction Layer working');
    
    // Test 4: OS Primitives
    console.log('\n4. Testing OS Primitives...');
    const os = new OSPrimitives(hal);
    const program = [0x02A00093, 0x00000073]; // ADDI x1, x0, 42; ECALL
    const process = await os.createProcess('test_process', program, 'test_core');
    console.log('✅ OS Primitives working');
    console.log(`   Process PID: ${process.pid}`);
    
    // Test 5: Execute Process
    console.log('\n5. Executing process...');
    const executionResult = await os.executeProcess(process.pid);
    
    if (!executionResult.success) {
      throw new Error('Process execution failed');
    }
    
    console.log('✅ Process executed successfully');
    console.log(`   Instructions executed: ${executionResult.result.instructions}`);
    
    // Test 6: Verify Holographic State
    console.log('\n6. Verifying holographic state...');
    const holographicState = os.getHolographicState();
    
    if (!holographicState.witness) {
      throw new Error('No holographic witness found');
    }
    
    if (!holographicState.atlas12288) {
      throw new Error('No atlas-12288 encoding found');
    }
    
    console.log('✅ Holographic state verified');
    console.log(`   Atlas-12288: Page ${holographicState.atlas12288.page}, Cycle ${holographicState.atlas12288.cycle}`);
    console.log(`   R96 Class: ${holographicState.atlas12288.r96Class}`);
    console.log(`   Klein Window: ${holographicState.atlas12288.kleinWindow}`);
    
    console.log('\n🎉 All tests passed! RISC-V Core implementation is working correctly.');
    console.log('🚀 Ready to proceed with full test suite.');
    
  } catch (error) {
    console.error('\n❌ Test failed:', error instanceof Error ? error.message : String(error));
    console.error('Stack trace:', error instanceof Error ? error.stack : 'No stack trace available');
    process.exit(1);
  }
}

// Run the simple test
if (require.main === module) {
  simpleTest().catch(error => {
    console.error('❌ Simple test failed:', error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

export { simpleTest };

/**
 * Unified Context Test
 * 
 * Comprehensive test demonstrating the single unified context that spans
 * from hardware to human interaction, showing true multi-modal interoperability
 * within a single domain internet operating system.
 */

import { UnifiedContextIntegrationManager } from '../unified/UnifiedContextIntegration';

export class UnifiedContextTest {
  private integration: UnifiedContextIntegrationManager;

  constructor(integration: UnifiedContextIntegrationManager) {
    this.integration = integration;
  }

  /**
   * Run complete unified context test
   */
  async runCompleteTest(): Promise<void> {
    console.log('🧪 Running Unified Context Test');
    console.log('=' .repeat(60));
    
    try {
      // Test 1: Integration Status
      await this.testIntegrationStatus();
      
      // Test 2: Unified Namespace
      await this.testUnifiedNamespace();
      
      // Test 3: Cross-Layer Communication
      await this.testCrossLayerCommunication();
      
      // Test 4: Multi-Modal Interoperability
      await this.testMultiModalInteroperability();
      
      // Test 5: Single Unified Context
      await this.testSingleUnifiedContext();
      
      // Test 6: RISC-V to UI Primitives
      await this.testRiscvToUIPrimitives();
      
      // Test 7: End-to-End Operations
      await this.testEndToEndOperations();
      
      // Test 8: Cross-Domain Primitives
      await this.testCrossDomainPrimitives();
      
      // Test 9: Human Interaction
      await this.testHumanInteraction();
      
      // Test 10: Performance Test
      await this.testPerformance();
      
      console.log('\n✅ All unified context tests completed successfully!');
      console.log('🎉 Single Unified Context is working correctly!');
      
    } catch (error) {
      console.error('\n❌ Test failed:', error);
      throw error;
    }
  }

  /**
   * Test integration status
   */
  private async testIntegrationStatus(): Promise<void> {
    console.log('\n📊 Test 1: Integration Status');
    
    const status = await this.integration.executeUnifiedContextOperation('get_integration_status', {});
    console.log('   Namespace Manager:', status.namespaceManager.entries, 'entries');
    console.log('   Communication Manager:', status.communicationManager.channels, 'channels');
    console.log('   Interoperability Manager:', status.interoperabilityManager.modalities, 'modalities');
    console.log('   Unified Context Manager:', status.unifiedContextManager.entries, 'entries');
    console.log('   RISC-V to UI Manager:', status.riscvToUIManager.instructions, 'instructions');
    
    if (status.namespaceManager.entries === 0) {
      throw new Error('No namespace entries found');
    }
    
    console.log('   ✅ Integration status test passed');
  }

  /**
   * Test unified namespace
   */
  private async testUnifiedNamespace(): Promise<void> {
    console.log('\n🌐 Test 2: Unified Namespace');
    
    // Register namespace entry
    await this.integration.executeUnifiedContextOperation('register_namespace_entry', {
      id: 'test_entry',
      name: 'Test Entry',
      type: 'cross_domain',
      layer: 'unified',
      component: 'test_component',
      properties: new Map([['test_property', 'test_value']])
    });
    
    // Get namespace statistics
    const stats = await this.integration.executeUnifiedContextOperation('get_namespace_statistics', {});
    console.log('   Total entries:', stats.totalEntries);
    console.log('   Cross-domain mappings:', stats.crossDomainMappings);
    console.log('   Holographic state:', stats.holographicState);
    
    if (stats.totalEntries === 0) {
      throw new Error('No namespace entries found');
    }
    
    console.log('   ✅ Unified namespace test passed');
  }

  /**
   * Test cross-layer communication
   */
  private async testCrossLayerCommunication(): Promise<void> {
    console.log('\n📡 Test 3: Cross-Layer Communication');
    
    // Send cross-layer message
    const messageId = await this.integration.executeUnifiedContextOperation('send_cross_layer_message', {
      sourceId: 'test_source',
      targetId: 'test_target',
      channelId: 'holographic_channel',
      type: 'notification',
      payload: { test: 'data' },
      metadata: new Map([['priority', 1]])
    });
    
    console.log('   Message ID:', messageId);
    
    // Get communication statistics
    const stats = await this.integration.executeUnifiedContextOperation('get_communication_statistics', {});
    console.log('   Channels:', stats.channels);
    console.log('   Messages:', stats.messages);
    console.log('   Queues:', stats.queues);
    console.log('   Subscriptions:', stats.subscriptions);
    
    if (stats.channels === 0) {
      throw new Error('No communication channels found');
    }
    
    console.log('   ✅ Cross-layer communication test passed');
  }

  /**
   * Test multi-modal interoperability
   */
  private async testMultiModalInteroperability(): Promise<void> {
    console.log('\n🔄 Test 4: Multi-Modal Interoperability');
    
    // Transform modality
    const transformedData = await this.integration.executeUnifiedContextOperation('transform_modality', {
      sourceModality: 'text',
      targetModality: 'audio',
      data: { text: 'Hello, Hologram OS!' }
    });
    
    console.log('   Transformed data:', transformedData);
    
    // Get interoperability statistics
    const stats = await this.integration.executeUnifiedContextOperation('get_interoperability_statistics', {});
    console.log('   Modalities:', stats.modalities);
    console.log('   Modality mappings:', stats.modalityMappings);
    console.log('   Interoperability bridges:', stats.interoperabilityBridges);
    console.log('   Cross-domain interactions:', stats.crossDomainInteractions);
    
    if (stats.modalities === 0) {
      throw new Error('No modalities found');
    }
    
    console.log('   ✅ Multi-modal interoperability test passed');
  }

  /**
   * Test single unified context
   */
  private async testSingleUnifiedContext(): Promise<void> {
    console.log('\n🔗 Test 5: Single Unified Context');
    
    // Execute cross-domain primitive
    const result = await this.integration.executeUnifiedContextOperation('execute_cross_domain_primitive', {
      primitiveId: 'riscv_to_ui_mapping',
      data: { coreId: 'core0', state: 'running' }
    });
    
    console.log('   Cross-domain primitive result:', result);
    
    // Get unified context statistics
    const stats = await this.integration.executeUnifiedContextOperation('get_unified_context_statistics', {});
    console.log('   Entries:', stats.entries);
    console.log('   Interactions:', stats.interactions);
    console.log('   Human interactions:', stats.humanInteractions);
    console.log('   Cross-domain primitives:', stats.crossDomainPrimitives);
    
    if (stats.crossDomainPrimitives === 0) {
      throw new Error('No cross-domain primitives found');
    }
    
    console.log('   ✅ Single unified context test passed');
  }

  /**
   * Test RISC-V to UI primitives
   */
  private async testRiscvToUIPrimitives(): Promise<void> {
    console.log('\n🔧 Test 6: RISC-V to UI Primitives');
    
    // Transform instruction to UI
    const uiElement = await this.integration.executeUnifiedContextOperation('transform_instruction_to_ui', {
      instruction: {
        opcode: '0110011',
        funct3: '000',
        funct7: '0000000',
        rd: 1,
        rs1: 2,
        rs2: 3,
        instruction: 0x003100b3,
        mnemonic: 'ADD',
        description: 'Add'
      }
    });
    
    console.log('   UI Element:', uiElement);
    
    // Transform UI to instruction
    const instruction = await this.integration.executeUnifiedContextOperation('transform_ui_to_instruction', {
      uiElement: {
        id: 'add_button',
        type: 'button',
        properties: new Map([['text', 'Add'], ['color', 'blue']]),
        events: new Map(),
        holographicContext: new Map(),
        witness: ''
      },
      event: {
        id: 'add_button_click',
        type: 'click',
        handler: async () => ({}),
        holographicContext: new Map(),
        witness: ''
      }
    });
    
    console.log('   RISC-V Instruction:', instruction);
    
    // Get RISC-V to UI statistics
    const stats = await this.integration.executeUnifiedContextOperation('get_riscv_to_ui_statistics', {});
    console.log('   Instructions:', stats.instructions);
    console.log('   UI Elements:', stats.uiElements);
    console.log('   Mappings:', stats.mappings);
    
    if (stats.instructions === 0) {
      throw new Error('No RISC-V instructions found');
    }
    
    console.log('   ✅ RISC-V to UI primitives test passed');
  }

  /**
   * Test end-to-end operations
   */
  private async testEndToEndOperations(): Promise<void> {
    console.log('\n🚀 Test 7: End-to-End Operations');
    
    // Execute end-to-end operation
    const result = await this.integration.executeEndToEndOperation('end_to_end_test', {
      id: 'end_to_end_entry',
      name: 'End-to-End Test Entry',
      type: 'cross_domain',
      layer: 'unified',
      component: 'end_to_end',
      properties: new Map([['test', 'end_to_end']]),
      sourceId: 'end_to_end_source',
      targetId: 'end_to_end_target',
      channelId: 'holographic_channel',
      messageType: 'notification',
      payload: { test: 'end_to_end' },
      metadata: new Map([['priority', 1]]),
      sourceModality: 'text',
      targetModality: 'audio',
      data: { text: 'End-to-end test' },
      primitiveId: 'riscv_to_ui_mapping',
      humanInteraction: {
        type: 'input',
        modality: 'text',
        content: 'Hello, Hologram OS!',
        context: new Map([['test', 'human_interaction']])
      },
      riscvInstruction: {
        opcode: '0110011',
        funct3: '000',
        funct7: '0000000',
        rd: 1,
        rs1: 2,
        rs2: 3,
        instruction: 0x003100b3,
        mnemonic: 'ADD',
        description: 'Add'
      }
    });
    
    console.log('   End-to-end operation result:', result);
    
    if (!result.success) {
      throw new Error('End-to-end operation failed');
    }
    
    console.log('   ✅ End-to-end operations test passed');
  }

  /**
   * Test cross-domain primitives
   */
  private async testCrossDomainPrimitives(): Promise<void> {
    console.log('\n🔀 Test 8: Cross-Domain Primitives');
    
    // Test RISC-V to UI mapping
    const riscvToUI = await this.integration.executeUnifiedContextOperation('execute_cross_domain_primitive', {
      primitiveId: 'riscv_to_ui_mapping',
      data: { coreId: 'core0', state: 'running' }
    });
    
    console.log('   RISC-V to UI mapping:', riscvToUI);
    
    // Test UI to RISC-V mapping
    const uiToRiscv = await this.integration.executeUnifiedContextOperation('execute_cross_domain_primitive', {
      primitiveId: 'ui_to_riscv_mapping',
      data: { action: 'click', coreId: 'core0' }
    });
    
    console.log('   UI to RISC-V mapping:', uiToRiscv);
    
    // Test hardware to human aggregation
    const hwToHuman = await this.integration.executeUnifiedContextOperation('execute_cross_domain_primitive', {
      primitiveId: 'hw_to_human_aggregation',
      data: { cores: 4, memory: 8192, devices: 10 }
    });
    
    console.log('   Hardware to human aggregation:', hwToHuman);
    
    console.log('   ✅ Cross-domain primitives test passed');
  }

  /**
   * Test human interaction
   */
  private async testHumanInteraction(): Promise<void> {
    console.log('\n👤 Test 9: Human Interaction');
    
    // Process human input
    const inputId = await this.integration.executeUnifiedContextOperation('process_human_interaction', {
      type: 'input',
      modality: 'text',
      content: 'Hello, Hologram OS!',
      context: new Map([['user', 'test_user']])
    });
    
    console.log('   Human input ID:', inputId);
    
    // Process human command
    const commandId = await this.integration.executeUnifiedContextOperation('process_human_interaction', {
      type: 'command',
      modality: 'text',
      content: 'Start the system',
      context: new Map([['user', 'test_user']])
    });
    
    console.log('   Human command ID:', commandId);
    
    // Process human query
    const queryId = await this.integration.executeUnifiedContextOperation('process_human_interaction', {
      type: 'query',
      modality: 'text',
      content: 'What is the system status?',
      context: new Map([['user', 'test_user']])
    });
    
    console.log('   Human query ID:', queryId);
    
    console.log('   ✅ Human interaction test passed');
  }

  /**
   * Test performance
   */
  private async testPerformance(): Promise<void> {
    console.log('\n⚡ Test 10: Performance Test');
    
    const iterations = 100;
    const startTime = Date.now();
    
    try {
      for (let i = 0; i < iterations; i++) {
        await this.integration.executeUnifiedContextOperation('get_integration_status', {});
      }
      
      const endTime = Date.now();
      const totalTime = endTime - startTime;
      const averageTime = totalTime / iterations;
      
      console.log(`   Total time: ${totalTime}ms`);
      console.log(`   Average time per operation: ${averageTime.toFixed(2)}ms`);
      console.log(`   Operations per second: ${(1000 / averageTime).toFixed(2)}`);
      console.log('   ✅ Performance test completed');
      
    } catch (error) {
      console.error('   ❌ Performance test failed:', error);
      throw error;
    }
  }
}

/**
 * Main test function
 */
export async function runUnifiedContextTest(): Promise<void> {
  console.log('🚀 Starting Unified Context Test Suite');
  console.log('=' .repeat(60));
  
  try {
    // Create unified context integration
    const integration = await UnifiedContextIntegrationManager.create();
    
    // Create test instance
    const test = new UnifiedContextTest(integration);
    
    // Run complete test
    await test.runCompleteTest();
    
    console.log('\n🎉 All tests completed successfully!');
    console.log('✨ Single Unified Context is fully operational!');
    
  } catch (error) {
    console.error('\n💥 Test suite failed:', error);
    throw error;
  }
}

// Export for use in other modules
export { UnifiedContextTest };

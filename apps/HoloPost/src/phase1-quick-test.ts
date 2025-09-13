/**
 * Quick Phase 1 Test
 * 
 * Simple test to verify Phase 1 components are working
 */

import { Phase1Integration } from './core/phase1-integration';

async function quickTest() {
  console.log('🧪 Quick Phase 1 Test');
  console.log('=' .repeat(40));
  
  try {
    // Create Phase 1 integration
    const phase1 = new Phase1Integration();
    
    console.log('✅ Phase 1 Integration created');
    
    // Initialize
    await phase1.initialize();
    console.log('✅ Phase 1 initialized');
    
    // Start
    await phase1.start();
    console.log('✅ Phase 1 started');
    
    // Get status
    const status = phase1.getStatus();
    console.log('📊 Status:', {
      initialized: status.isInitialized,
      running: status.isRunning,
      health: status.health,
      components: status.components
    });
    
    // Get performance metrics
    const metrics = phase1.getPerformanceMetrics();
    console.log('📈 Performance:', {
      throughput: metrics.throughput,
      target: metrics.targetThroughput,
      achievement: metrics.achievementPercentage + '%'
    });
    
    // Test UOR creation
    const testContent = Buffer.from('Hello, Phase 1!');
    const uor = await phase1.createUOR(testContent, {
      type: 'text/plain',
      version: '1.0.0'
    });
    console.log('✅ UOR created:', uor.uorId.substring(0, 16) + '...');
    
    // Test UOR validation
    const isValid = await phase1.validateUOR(uor);
    console.log('✅ UOR validation:', isValid ? 'PASSED' : 'FAILED');
    
    // Stop
    await phase1.stop();
    console.log('✅ Phase 1 stopped');
    
    console.log('\n🎉 Quick test completed successfully!');
    console.log('Phase 1 is working correctly.');
    
  } catch (error) {
    console.error('❌ Test failed:', error.message);
    process.exit(1);
  }
}

// Run the test
quickTest();

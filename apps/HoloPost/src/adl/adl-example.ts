/**
 * Advanced Data Layouts (ADLs) - Complete System Example
 * 
 * This example demonstrates the complete ADL system implementation including:
 * - Content-addressable storage
 * - Block storage properties
 * - Built-in integrity verification
 * - Holographic verification
 * - Performance optimization
 * - Integration with existing systems
 */

import { ADLIntegrationManager, ADLIntegrationConfig } from './adl-integration';
import { EnhancedADLCore, EnhancedADLConfig } from './adl-enhanced-core';
import { ContentAddressableStorage } from './adl-content-addressable';
import { BlockStorageSystem, BlockStorageConfig } from './adl-block-storage';
import { IntegritySystem, IntegrityConfig } from './adl-integrity-system';

/**
 * Example: Complete ADL System Usage
 */
export async function demonstrateCompleteADLSystem(): Promise<void> {
  console.log('🚀 Starting Complete ADL System Demonstration');
  
  // Configuration for the complete ADL system
  const adlConfig: ADLIntegrationConfig = {
    enhancedADL: {
      contentAddressable: {
        enabled: true,
        compressionEnabled: true,
        deduplicationEnabled: true,
        replicationFactor: 3
      },
      blockStorage: {
        blockSize: 64 * 1024, // 64KB blocks
        replicationFactor: 3,
        erasureCoding: { k: 6, m: 3 },
        placementStrategy: 'holographic',
        integrityCheckInterval: 30000, // 30 seconds
        holographicVerification: true,
        compressionEnabled: true,
        encryptionEnabled: true
      },
      integrity: {
        enabled: true,
        checkInterval: 10000, // 10 seconds
        holographicVerification: true,
        merkleTreeVerification: true,
        cryptographicSignatures: true,
        realTimeMonitoring: true,
        autoRemediation: true,
        alertThresholds: {
          integrityScore: 0.95,
          violationCount: 5,
          checkFailureRate: 0.05
        }
      },
      performance: {
        cacheSize: 10000,
        batchSize: 100,
        parallelProcessing: true,
        optimizationLevel: 'maximum'
      },
      holographic: {
        enabled: true,
        verificationLevel: 'maximum',
        fingerprintAlgorithm: 'holographic-sha256'
      }
    },
    firebaseCompatibility: {
      enabled: true,
      realTimeSync: true,
      authentication: true
    },
    performance: {
      optimizationEnabled: true,
      targetThroughput: 25, // 25 GB/s
      cacheSize: 10000,
      batchSize: 100
    },
    holographic: {
      enabled: true,
      verificationLevel: 'maximum',
      fingerprintAlgorithm: 'holographic-sha256'
    }
  };

  // Initialize the ADL integration manager
  const adlManager = new ADLIntegrationManager(adlConfig);
  
  // Set up event listeners
  setupEventListeners(adlManager);
  
  try {
    // Initialize the system
    console.log('📋 Initializing ADL System...');
    await adlManager.initialize();
    console.log('✅ ADL System initialized successfully');

    // Demonstrate user profile creation
    console.log('\n👤 Creating User Profile...');
    const userProfile = await adlManager.createUserProfile({
      id: 'user-123',
      email: 'john.doe@example.com',
      displayName: 'John Doe',
      photoURL: 'https://example.com/photo.jpg',
      preferences: {
        theme: 'dark',
        notifications: true,
        language: 'en'
      }
    });
    console.log('✅ User profile created:', userProfile.id);

    // Demonstrate document creation
    console.log('\n📄 Creating Document...');
    const document = await adlManager.createDocument({
      id: 'doc-456',
      title: 'ADL System Documentation',
      content: 'This is a comprehensive document about the Advanced Data Layouts system...',
      authorId: 'user-123',
      tags: ['documentation', 'adl', 'system'],
      isPublished: true
    });
    console.log('✅ Document created:', document.id);

    // Demonstrate message creation
    console.log('\n💬 Creating Message...');
    const message = await adlManager.createMessage({
      id: 'msg-789',
      senderId: 'user-123',
      recipientId: 'user-456',
      content: 'Hello! This is a test message using the ADL system.',
      messageType: 'text',
      isEncrypted: false
    });
    console.log('✅ Message created:', message.id);

    // Demonstrate querying
    console.log('\n🔍 Querying Instances...');
    const userProfiles = await adlManager.queryInstances({
      schemaId: 'user_profile',
      filters: [
        { field: 'isActive', operator: 'eq', value: true }
      ],
      orderBy: [
        { field: 'createdAt', direction: 'desc' }
      ],
      limit: 10,
      includeContentAddress: true,
      includeIntegrityProof: true,
      holographicVerification: true
    });
    console.log(`✅ Found ${userProfiles.length} active user profiles`);

    // Demonstrate integrity verification
    console.log('\n🔒 Verifying Instance Integrity...');
    const isUserValid = await adlManager.verifyInstanceIntegrity('user-123');
    const isDocValid = await adlManager.verifyInstanceIntegrity('doc-456');
    const isMsgValid = await adlManager.verifyInstanceIntegrity('msg-789');
    console.log(`✅ Integrity verification results: User=${isUserValid}, Document=${isDocValid}, Message=${isMsgValid}`);

    // Demonstrate updating
    console.log('\n📝 Updating Document...');
    const updatedDocument = await adlManager.updateInstance('doc-456', {
      content: 'This is an updated comprehensive document about the Advanced Data Layouts system with new information...',
      updatedAt: new Date().toISOString(),
      version: 2
    });
    console.log('✅ Document updated:', updatedDocument.id);

    // Get comprehensive statistics
    console.log('\n📊 Getting System Statistics...');
    const stats = await adlManager.getStats();
    console.log('✅ System Statistics:');
    console.log(`   - Total Schemas: ${stats.enhancedADL.core.totalSchemas}`);
    console.log(`   - Total Instances: ${stats.enhancedADL.core.totalInstances}`);
    console.log(`   - Cache Hit Rate: ${(stats.enhancedADL.core.cacheHitRate * 100).toFixed(2)}%`);
    console.log(`   - Integrity Score: ${(stats.enhancedADL.integrity.integrityScore * 100).toFixed(2)}%`);
    console.log(`   - Content Addressable Storage: ${stats.enhancedADL.contentAddressable.totalContent} items`);
    console.log(`   - Block Storage: ${stats.enhancedADL.blockStorage.totalBlocks} blocks`);
    console.log(`   - Total Violations: ${stats.enhancedADL.integrity.violations}`);

    // Demonstrate individual component usage
    console.log('\n🔧 Demonstrating Individual Components...');
    await demonstrateIndividualComponents();

    console.log('\n🎉 Complete ADL System Demonstration Finished Successfully!');

  } catch (error) {
    console.error('❌ Error during ADL system demonstration:', error);
  } finally {
    // Cleanup
    console.log('\n🧹 Cleaning up...');
    await adlManager.close();
    console.log('✅ Cleanup completed');
  }
}

/**
 * Demonstrate individual ADL components
 */
async function demonstrateIndividualComponents(): Promise<void> {
  console.log('🔧 Demonstrating Individual ADL Components...');

  // Content-Addressable Storage
  console.log('\n📦 Content-Addressable Storage:');
  const contentStore = new ContentAddressableStorage();
  
  const testData = Buffer.from('This is test data for content-addressable storage');
  const contentAddress = await contentStore.put(testData, {
    mimeType: 'text/plain',
    encoding: 'utf8'
  });
  console.log(`   - Content stored with hash: ${contentAddress.hash.substring(0, 16)}...`);
  
  const retrievedData = await contentStore.get(contentAddress);
  console.log(`   - Content retrieved: ${retrievedData ? 'Success' : 'Failed'}`);
  
  const stats = await contentStore.getStats();
  console.log(`   - Total content: ${stats.totalContent}, Total size: ${stats.totalSize} bytes`);
  
  await contentStore.close();

  // Block Storage System
  console.log('\n🧱 Block Storage System:');
  const blockConfig: BlockStorageConfig = {
    blockSize: 32 * 1024, // 32KB blocks
    replicationFactor: 2,
    erasureCoding: { k: 4, m: 2 },
    placementStrategy: 'consistent-hash',
    integrityCheckInterval: 15000,
    holographicVerification: true,
    compressionEnabled: true,
    encryptionEnabled: false
  };
  
  const blockStorage = new BlockStorageSystem(blockConfig);
  
  const largeData = Buffer.alloc(100 * 1024, 'A'); // 100KB of 'A's
  const blockIds = await blockStorage.write(largeData, 'application/octet-stream');
  console.log(`   - Data written as ${blockIds.length} blocks`);
  
  const reconstructedData = await blockStorage.read(blockIds);
  console.log(`   - Data reconstructed: ${reconstructedData ? 'Success' : 'Failed'}`);
  
  const blockStats = blockStorage.getStats();
  console.log(`   - Total blocks: ${blockStats.totalBlocks}, Total size: ${blockStats.totalSize} bytes`);
  
  await blockStorage.close();

  // Integrity System
  console.log('\n🔒 Integrity System:');
  const integrityConfig: IntegrityConfig = {
    enabled: true,
    checkInterval: 5000,
    holographicVerification: true,
    merkleTreeVerification: true,
    cryptographicSignatures: true,
    realTimeMonitoring: true,
    autoRemediation: true,
    alertThresholds: {
      integrityScore: 0.9,
      violationCount: 3,
      checkFailureRate: 0.1
    }
  };
  
  const integritySystem = new IntegritySystem(integrityConfig);
  
  const testData2 = Buffer.from('This is test data for integrity verification');
  const integrityProof = await integritySystem.verifyIntegrity('test-data-1', testData2);
  console.log(`   - Integrity proof created: ${integrityProof.valid ? 'Valid' : 'Invalid'}`);
  console.log(`   - Confidence: ${(integrityProof.confidence * 100).toFixed(2)}%`);
  
  const proofValid = await integritySystem.verifyProof(integrityProof.id);
  console.log(`   - Proof verification: ${proofValid ? 'Valid' : 'Invalid'}`);
  
  const integrityStats = integritySystem.getMetrics();
  console.log(`   - Total checks: ${integrityStats.totalChecks}, Integrity score: ${(integrityStats.integrityScore * 100).toFixed(2)}%`);
  
  await integritySystem.close();

  console.log('✅ Individual components demonstration completed');
}

/**
 * Set up event listeners for the ADL manager
 */
function setupEventListeners(adlManager: ADLIntegrationManager): void {
  // Core events
  adlManager.on('initialized', (event) => {
    console.log('🎯 ADL System initialized at', new Date(event.timestamp).toISOString());
  });

  adlManager.on('userProfileCreated', (event) => {
    console.log('👤 User profile created:', event.userData.email);
  });

  adlManager.on('documentCreated', (event) => {
    console.log('📄 Document created:', event.documentData.title);
  });

  adlManager.on('messageCreated', (event) => {
    console.log('💬 Message created:', event.messageData.content.substring(0, 50) + '...');
  });

  adlManager.on('instanceUpdated', (event) => {
    console.log('📝 Instance updated:', event.instanceId);
  });

  adlManager.on('integrityVerified', (event) => {
    console.log('🔒 Integrity verified:', event.instanceId, event.isValid ? '✅' : '❌');
  });

  // Performance events
  adlManager.on('performanceMetrics', (event) => {
    console.log('📊 Performance metrics updated');
  });

  adlManager.on('holographicMetrics', (event) => {
    console.log('🔮 Holographic metrics updated');
  });

  // Error events
  adlManager.on('initializationError', (event) => {
    console.error('❌ Initialization error:', event.error);
  });

  adlManager.on('firebaseSyncError', (event) => {
    console.error('❌ Firebase sync error:', event.error);
  });

  adlManager.on('adlIntegrityViolation', (event) => {
    console.warn('⚠️ ADL integrity violation detected:', event.violation);
  });
}

/**
 * Performance benchmark for ADL system
 */
export async function benchmarkADLSystem(): Promise<void> {
  console.log('🏁 Starting ADL System Performance Benchmark');
  
  const adlConfig: ADLIntegrationConfig = {
    enhancedADL: {
      contentAddressable: {
        enabled: true,
        compressionEnabled: true,
        deduplicationEnabled: true,
        replicationFactor: 3
      },
      blockStorage: {
        blockSize: 64 * 1024,
        replicationFactor: 3,
        erasureCoding: { k: 6, m: 3 },
        placementStrategy: 'holographic',
        integrityCheckInterval: 30000,
        holographicVerification: true,
        compressionEnabled: true,
        encryptionEnabled: true
      },
      integrity: {
        enabled: true,
        checkInterval: 10000,
        holographicVerification: true,
        merkleTreeVerification: true,
        cryptographicSignatures: true,
        realTimeMonitoring: true,
        autoRemediation: true,
        alertThresholds: {
          integrityScore: 0.95,
          violationCount: 5,
          checkFailureRate: 0.05
        }
      },
      performance: {
        cacheSize: 10000,
        batchSize: 100,
        parallelProcessing: true,
        optimizationLevel: 'maximum'
      },
      holographic: {
        enabled: true,
        verificationLevel: 'maximum',
        fingerprintAlgorithm: 'holographic-sha256'
      }
    },
    firebaseCompatibility: {
      enabled: false, // Disable for benchmark
      realTimeSync: false,
      authentication: false
    },
    performance: {
      optimizationEnabled: true,
      targetThroughput: 25,
      cacheSize: 10000,
      batchSize: 100
    },
    holographic: {
      enabled: true,
      verificationLevel: 'maximum',
      fingerprintAlgorithm: 'holographic-sha256'
    }
  };

  const adlManager = new ADLIntegrationManager(adlConfig);
  
  try {
    await adlManager.initialize();
    
    const iterations = 1000;
    const startTime = Date.now();
    
    // Benchmark instance creation
    console.log(`📊 Benchmarking ${iterations} instance creations...`);
    const createStartTime = Date.now();
    
    for (let i = 0; i < iterations; i++) {
      await adlManager.createUserProfile({
        id: `benchmark-user-${i}`,
        email: `user${i}@benchmark.com`,
        displayName: `Benchmark User ${i}`
      });
    }
    
    const createTime = Date.now() - createStartTime;
    const createThroughput = iterations / (createTime / 1000);
    
    console.log(`✅ Creation benchmark: ${createThroughput.toFixed(2)} instances/second`);
    
    // Benchmark queries
    console.log(`📊 Benchmarking ${iterations} queries...`);
    const queryStartTime = Date.now();
    
    for (let i = 0; i < iterations; i++) {
      await adlManager.queryInstances({
        schemaId: 'user_profile',
        filters: [{ field: 'isActive', operator: 'eq', value: true }],
        limit: 10
      });
    }
    
    const queryTime = Date.now() - queryStartTime;
    const queryThroughput = iterations / (queryTime / 1000);
    
    console.log(`✅ Query benchmark: ${queryThroughput.toFixed(2)} queries/second`);
    
    // Get final statistics
    const stats = await adlManager.getStats();
    const totalTime = Date.now() - startTime;
    
    console.log('\n📊 Benchmark Results:');
    console.log(`   - Total time: ${totalTime}ms`);
    console.log(`   - Creation throughput: ${createThroughput.toFixed(2)} instances/second`);
    console.log(`   - Query throughput: ${queryThroughput.toFixed(2)} queries/second`);
    console.log(`   - Total instances: ${stats.enhancedADL.core.totalInstances}`);
    console.log(`   - Cache hit rate: ${(stats.enhancedADL.core.cacheHitRate * 100).toFixed(2)}%`);
    console.log(`   - Integrity score: ${(stats.enhancedADL.integrity.integrityScore * 100).toFixed(2)}%`);
    
  } catch (error) {
    console.error('❌ Benchmark error:', error);
  } finally {
    await adlManager.close();
  }
}

// Export the main demonstration function
export { demonstrateCompleteADLSystem as runADLDemonstration };

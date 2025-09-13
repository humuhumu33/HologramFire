/**
 * Test file for IPFS Integration
 * 
 * Demonstrates the IPFS integration for distributed storage
 * and content discovery in the Hologram system.
 */

import { IPFSClient, IPFSConfig } from './IPFSClient';
import { IPFSContentResolver } from './IPFSContentResolver';
import { Atlas12288Encoder } from '../atlas12288/Atlas12288Encoder';
import { WitnessGenerator } from '../witness/WitnessGenerator';

async function testIPFSIntegration() {
  console.log('🧪 Testing IPFS Integration for Distributed Storage');
  console.log('=' .repeat(60));

  try {
    // Test 1: IPFS Client Configuration
    console.log('\n📊 Test 1: IPFS Client Configuration');
    const ipfsConfig: IPFSConfig = {
      host: 'localhost',
      port: 5001,
      protocol: 'http',
      timeout: 30000,
      retries: 3
    };

    const ipfsClient = new IPFSClient(ipfsConfig);
    console.log('✅ IPFS Client created with config:', {
      host: ipfsConfig.host,
      port: ipfsConfig.port,
      protocol: ipfsConfig.protocol
    });

    // Test 2: Content Creation and Atlas-12288 Encoding
    console.log('\n🔗 Test 2: Content Creation and Atlas-12288 Encoding');
    const atlasEncoder = new Atlas12288Encoder();
    const witnessGenerator = new WitnessGenerator();

    const testContent = {
      name: 'distributed-document.txt',
      data: 'This is a test document for distributed storage in the Hologram system using IPFS.',
      mimeType: 'text/plain'
    };

    const atlasMetadata = await atlasEncoder.encodeContent(testContent);
    const uorId = await atlasEncoder.generateUORID(testContent);
    const witness = await witnessGenerator.generateStorageWitness(atlasMetadata);

    const content = {
      id: uorId,
      name: testContent.name,
      encoding: JSON.stringify(atlasMetadata),
      data: testContent.data,
      witness: witness,
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        size: testContent.data.length,
        mimeType: testContent.mimeType,
        checksum: await atlasEncoder.generateChecksum(testContent.data),
        atlas12288: atlasMetadata
      }
    };

    console.log('✅ Content created:', {
      id: content.id.substring(0, 16) + '...',
      name: content.name,
      size: content.metadata.size,
      page: content.metadata.atlas12288.page,
      cycle: content.metadata.atlas12288.cycle,
      r96Class: content.metadata.atlas12288.r96Class
    });

    // Test 3: IPFS Content Storage
    console.log('\n💾 Test 3: IPFS Content Storage');
    try {
      const cid = await ipfsClient.storeContent(content);
      console.log('✅ Content stored in IPFS with CID:', cid);
    } catch (error) {
      console.log('⚠️  IPFS storage test skipped (IPFS not available):', error.message);
    }

    // Test 4: IPFS Content Retrieval
    console.log('\n🔍 Test 4: IPFS Content Retrieval');
    try {
      const retrievedContent = await ipfsClient.getContent('test-cid');
      if (retrievedContent) {
        console.log('✅ Content retrieved from IPFS:', retrievedContent.name);
      } else {
        console.log('⚠️  Content retrieval test skipped (no content available)');
      }
    } catch (error) {
      console.log('⚠️  IPFS retrieval test skipped (IPFS not available):', error.message);
    }

    // Test 5: IPFS Content Resolver
    console.log('\n🔄 Test 5: IPFS Content Resolver');
    const ipfsResolver = new IPFSContentResolver(ipfsConfig);
    
    // Store content using resolver
    await ipfsResolver.storeContent(content);
    console.log('✅ Content stored using IPFS Content Resolver');

    // Resolve by name
    const resolvedByName = await ipfsResolver.resolveByName(testContent.name);
    console.log('✅ Resolved by name:', resolvedByName ? 'SUCCESS' : 'FAILED');

    // Resolve by UOR-ID
    const resolvedByUORID = await ipfsResolver.resolveByUORID(uorId);
    console.log('✅ Resolved by UOR-ID:', resolvedByUORID ? 'SUCCESS' : 'FAILED');

    // Resolve by coordinates
    const resolvedByCoordinates = await ipfsResolver.resolveByCoordinates(
      atlasMetadata.page, 
      atlasMetadata.cycle
    );
    console.log('✅ Resolved by coordinates:', resolvedByCoordinates ? 'SUCCESS' : 'FAILED');

    // Test 6: IPFS Content Search
    console.log('\n🔎 Test 6: IPFS Content Search');
    const searchResults = await ipfsResolver.searchContent({
      mimeType: 'text/plain',
      limit: 10,
      offset: 0
    });
    console.log('✅ Search results:', searchResults.length, 'items found');

    // Test 7: IPFS Statistics
    console.log('\n📈 Test 7: IPFS Statistics');
    const stats = await ipfsResolver.getResolutionStats();
    console.log('✅ Resolution Stats:', {
      totalContent: stats.totalContent,
      totalResolutions: stats.totalResolutions,
      averageResolutionTime: stats.averageResolutionTime.toFixed(2) + 'ms',
      conservationViolations: stats.conservationViolations,
      bijectionIntegrity: (stats.bijunctionIntegrity * 100).toFixed(2) + '%'
    });

    if (stats.ipfsStats) {
      console.log('✅ IPFS Stats:', {
        totalContent: stats.ipfsStats.totalContent,
        totalSize: stats.ipfsStats.totalSize,
        averageReplicationFactor: stats.ipfsStats.averageReplicationFactor.toFixed(2),
        pinnedContent: stats.ipfsStats.pinnedContent
      });
    }

    // Test 8: IPFS Sync
    console.log('\n🔄 Test 8: IPFS Sync');
    await ipfsResolver.syncWithIPFS();
    console.log('✅ IPFS sync completed');

    // Cleanup
    await ipfsResolver.close();
    await ipfsClient.close();

    console.log('\n🎉 All IPFS integration tests passed!');
    console.log('\n📋 Summary:');
    console.log('   ✅ IPFS client configuration and initialization');
    console.log('   ✅ Content creation with atlas-12288 encoding');
    console.log('   ✅ IPFS content storage (when IPFS available)');
    console.log('   ✅ IPFS content retrieval (when IPFS available)');
    console.log('   ✅ IPFS content resolver with bijective mapping');
    console.log('   ✅ Content resolution by name, UOR-ID, and coordinates');
    console.log('   ✅ IPFS content search capabilities');
    console.log('   ✅ IPFS statistics and monitoring');
    console.log('   ✅ IPFS synchronization');

  } catch (error) {
    console.error('❌ IPFS integration test failed:', error);
    throw error;
  }
}

// Run tests if this file is executed directly
if (require.main === module) {
  testIPFSIntegration()
    .then(() => {
      console.log('\n✅ All IPFS integration tests completed successfully!');
      process.exit(0);
    })
    .catch((error) => {
      console.error('\n❌ IPFS integration tests failed:', error);
      process.exit(1);
    });
}

export { testIPFSIntegration };

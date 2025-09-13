/**
 * Advanced Data Layouts (ADLs) - Complete System Export
 * 
 * This module exports all components of the comprehensive ADL system:
 * - Core ADL system with enhanced capabilities
 * - Content-addressable storage
 * - Block storage properties
 * - Built-in integrity verification
 * - Holographic verification
 * - Integration layer
 * - Example implementations
 */

// Core ADL System
export { ADLCore, ADLSchema, ADLInstance, ADLQuery, ADLValidationResult } from './adl-core';
export { 
  EnhancedADLCore, 
  EnhancedADLConfig, 
  EnhancedADLInstance, 
  EnhancedADLQuery, 
  EnhancedADLStats 
} from './adl-enhanced-core';

// Content-Addressable Storage
export {
  ContentAddressableStorage,
  ContentAddress,
  ContentMetadata,
  ContentBlock,
  MerkleTree,
  ContentStore,
  ContentStoreStats
} from './adl-content-addressable';

// Block Storage System
export {
  BlockStorageSystem,
  StorageBlock,
  BlockMetadata,
  BlockPlacement,
  ErasureShard,
  BlockIntegrity,
  BlockStorageConfig,
  BlockStorageStats
} from './adl-block-storage';

// Integrity System
export {
  IntegritySystem,
  IntegrityCheck,
  IntegrityProof,
  IntegrityViolation,
  IntegrityMetrics,
  IntegrityConfig
} from './adl-integrity-system';

// Schema Definitions
export {
  UserProfileSchema,
  DocumentSchema,
  MessageSchema,
  PerformanceMetricsSchema,
  AvailableSchemas,
  getSchemaById,
  getAllSchemaIds,
  validateSchemaCompatibility
} from './adl-schemas';

export {
  ContentAddressSchema,
  StorageBlockSchema,
  IntegrityProofSchema,
  SystemMetricsSchema,
  EnhancedSchemas,
  getEnhancedSchemaById,
  getAllEnhancedSchemaIds,
  validateEnhancedSchemaCompatibility
} from './adl-enhanced-schemas';

// Integration Layer
export {
  ADLIntegrationManager,
  ADLIntegrationConfig,
  ADLIntegrationStats
} from './adl-integration';

// Examples and Demonstrations
export {
  demonstrateCompleteADLSystem,
  benchmarkADLSystem,
  runADLDemonstration
} from './adl-example';

// Type Definitions
export type {
  ADLField,
  ADLType,
  ADLConstraint,
  ADLFieldConstraint,
  ADLIndex,
  ADLValidationError,
  ADLValidationWarning,
  ADLQueryFilter,
  ADLOrderBy
} from './adl-core';

export type {
  StorageLocation,
  ContentAddress,
  ContentMetadata,
  ContentBlock,
  MerkleTree,
  ContentStore,
  ContentStoreStats
} from './adl-content-addressable';

export type {
  StorageBlock,
  BlockMetadata,
  BlockPlacement,
  ErasureShard,
  BlockIntegrity,
  BlockStorageConfig,
  BlockStorageStats
} from './adl-block-storage';

export type {
  IntegrityCheck,
  IntegrityProof,
  IntegrityViolation,
  IntegrityMetrics,
  IntegrityConfig
} from './adl-integrity-system';

export type {
  EnhancedADLConfig,
  EnhancedADLInstance,
  EnhancedADLQuery,
  EnhancedADLStats
} from './adl-enhanced-core';

export type {
  ADLIntegrationConfig,
  ADLIntegrationStats
} from './adl-integration';

/**
 * Default configuration for the complete ADL system
 */
export const DEFAULT_ADL_CONFIG: ADLIntegrationConfig = {
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

/**
 * Create a new ADL integration manager with default configuration
 */
export function createADLManager(config?: Partial<ADLIntegrationConfig>): ADLIntegrationManager {
  const finalConfig = { ...DEFAULT_ADL_CONFIG, ...config };
  return new ADLIntegrationManager(finalConfig);
}

/**
 * Create a new enhanced ADL core with default configuration
 */
export function createEnhancedADLCore(config?: Partial<EnhancedADLConfig>): EnhancedADLCore {
  const defaultConfig: EnhancedADLConfig = {
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
  };

  const finalConfig = { ...defaultConfig, ...config };
  return new EnhancedADLCore(finalConfig);
}

/**
 * Version information for the ADL system
 */
export const ADL_VERSION = {
  major: 1,
  minor: 0,
  patch: 0,
  build: '2024.01.01',
  description: 'Advanced Data Layouts (ADLs) - Complete System Implementation'
};

/**
 * System capabilities
 */
export const ADL_CAPABILITIES = {
  contentAddressableStorage: true,
  blockStorage: true,
  integrityVerification: true,
  holographicVerification: true,
  compression: true,
  encryption: true,
  deduplication: true,
  replication: true,
  erasureCoding: true,
  realTimeMonitoring: true,
  autoRemediation: true,
  performanceOptimization: true,
  firebaseCompatibility: true,
  parallelProcessing: true,
  caching: true,
  indexing: true,
  querying: true,
  transactions: true,
  consistency: true,
  availability: true
};

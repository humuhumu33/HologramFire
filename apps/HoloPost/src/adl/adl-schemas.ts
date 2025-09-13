/**
 * Advanced Data Layouts (ADLs) Schema Definitions
 * 
 * Features:
 * - Predefined schemas for common data types
 * - Schema validation and integrity checking
 * - Performance-optimized layouts
 * - Holographic verification schemas
 */

import { ADLSchema } from './adl-core';
import crypto from 'node:crypto';

/**
 * Generate holographic fingerprint for schema
 */
function generateHolographicFingerprint(schemaData: any): string {
  const schemaString = JSON.stringify(schemaData);
  return crypto.createHash('sha256').update(schemaString).digest('hex');
}

/**
 * User Profile Schema
 */
export const UserProfileSchema: ADLSchema = {
  id: 'user_profile',
  name: 'User Profile',
  version: '1.0.0',
  fields: [
    {
      name: 'id',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.id'),
        verificationRequired: true
      }
    },
    {
      name: 'email',
      type: { primitive: 'string', size: 255 },
      required: true,
      constraints: [
        { type: 'pattern', value: '^[\\w\\.-]+@[\\w\\.-]+\\.[a-zA-Z]{2,}$', message: 'Invalid email format' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.email'),
        verificationRequired: true
      }
    },
    {
      name: 'displayName',
      type: { primitive: 'string', size: 100 },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.displayName'),
        verificationRequired: false
      }
    },
    {
      name: 'photoURL',
      type: { primitive: 'string', size: 500 },
      required: false,
      constraints: [
        { type: 'pattern', value: '^https?://', message: 'Photo URL must be a valid HTTP/HTTPS URL' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.photoURL'),
        verificationRequired: false
      }
    },
    {
      name: 'createdAt',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.createdAt'),
        verificationRequired: false
      }
    },
    {
      name: 'lastLoginAt',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.lastLoginAt'),
        verificationRequired: false
      }
    },
    {
      name: 'isActive',
      type: { primitive: 'boolean' },
      required: true,
      defaultValue: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.isActive'),
        verificationRequired: false
      }
    },
    {
      name: 'preferences',
      type: { primitive: 'string', encoding: 'utf8' },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('user_profile.preferences'),
        verificationRequired: false
      }
    }
  ],
  constraints: [
    {
      type: 'unique',
      fields: ['id'],
      holographicWeight: 1.0
    },
    {
      type: 'unique',
      fields: ['email'],
      holographicWeight: 0.9
    },
    {
      type: 'holographic-integrity',
      fields: ['id', 'email'],
      holographicWeight: 0.8
    }
  ],
  indexes: [
    {
      name: 'user_profile_id_index',
      fields: ['id'],
      type: 'holographic',
      unique: true,
      performance: { cacheSize: 1000, compressionLevel: 0 }
    },
    {
      name: 'user_profile_email_index',
      fields: ['email'],
      type: 'btree',
      unique: true,
      performance: { cacheSize: 500, compressionLevel: 1 }
    },
    {
      name: 'user_profile_active_index',
      fields: ['isActive'],
      type: 'hash',
      unique: false,
      performance: { cacheSize: 100, compressionLevel: 2 }
    }
  ],
  holographicProperties: {
    fingerprint: generateHolographicFingerprint('user_profile_schema'),
    verificationLevel: 'enhanced',
    integrityChecks: ['field_validation', 'constraint_checking', 'holographic_verification', 'email_format_validation']
  },
  performance: {
    compressionEnabled: true,
    cacheStrategy: 'lru',
    memoryLayout: 'packed'
  }
};

/**
 * Document Schema
 */
export const DocumentSchema: ADLSchema = {
  id: 'document',
  name: 'Document',
  version: '1.0.0',
  fields: [
    {
      name: 'id',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('document.id'),
        verificationRequired: true
      }
    },
    {
      name: 'title',
      type: { primitive: 'string', size: 200 },
      required: true,
      constraints: [
        { type: 'min', value: 1, message: 'Title must not be empty' },
        { type: 'max', value: 200, message: 'Title must be less than 200 characters' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('document.title'),
        verificationRequired: true
      }
    },
    {
      name: 'content',
      type: { primitive: 'string', encoding: 'utf8' },
      required: true,
      constraints: [
        { type: 'min', value: 1, message: 'Content must not be empty' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('document.content'),
        verificationRequired: true
      }
    },
    {
      name: 'authorId',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('document.authorId'),
        verificationRequired: true
      }
    },
    {
      name: 'createdAt',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('document.createdAt'),
        verificationRequired: false
      }
    },
    {
      name: 'updatedAt',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('document.updatedAt'),
        verificationRequired: false
      }
    },
    {
      name: 'tags',
      type: { primitive: 'string', encoding: 'utf8' },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('document.tags'),
        verificationRequired: false
      }
    },
    {
      name: 'isPublished',
      type: { primitive: 'boolean' },
      required: true,
      defaultValue: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('document.isPublished'),
        verificationRequired: false
      }
    },
    {
      name: 'version',
      type: { primitive: 'number', precision: 0 },
      required: true,
      defaultValue: 1,
      constraints: [
        { type: 'min', value: 1, message: 'Version must be at least 1' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('document.version'),
        verificationRequired: false
      }
    }
  ],
  constraints: [
    {
      type: 'unique',
      fields: ['id'],
      holographicWeight: 1.0
    },
    {
      type: 'foreign-key',
      fields: ['authorId'],
      reference: { schema: 'user_profile', field: 'id' },
      holographicWeight: 0.8
    },
    {
      type: 'holographic-integrity',
      fields: ['id', 'title', 'content'],
      holographicWeight: 0.9
    }
  ],
  indexes: [
    {
      name: 'document_id_index',
      fields: ['id'],
      type: 'holographic',
      unique: true,
      performance: { cacheSize: 1000, compressionLevel: 0 }
    },
    {
      name: 'document_author_index',
      fields: ['authorId'],
      type: 'btree',
      unique: false,
      performance: { cacheSize: 500, compressionLevel: 1 }
    },
    {
      name: 'document_published_index',
      fields: ['isPublished'],
      type: 'hash',
      unique: false,
      performance: { cacheSize: 100, compressionLevel: 2 }
    },
    {
      name: 'document_created_index',
      fields: ['createdAt'],
      type: 'btree',
      unique: false,
      performance: { cacheSize: 200, compressionLevel: 1 }
    },
    {
      name: 'document_composite_index',
      fields: ['authorId', 'isPublished', 'createdAt'],
      type: 'composite',
      unique: false,
      performance: { cacheSize: 300, compressionLevel: 1 }
    }
  ],
  holographicProperties: {
    fingerprint: generateHolographicFingerprint('document_schema'),
    verificationLevel: 'maximum',
    integrityChecks: ['field_validation', 'constraint_checking', 'holographic_verification', 'foreign_key_validation', 'content_integrity']
  },
  performance: {
    compressionEnabled: true,
    cacheStrategy: 'lfu',
    memoryLayout: 'aligned'
  }
};

/**
 * Message Schema
 */
export const MessageSchema: ADLSchema = {
  id: 'message',
  name: 'Message',
  version: '1.0.0',
  fields: [
    {
      name: 'id',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.id'),
        verificationRequired: true
      }
    },
    {
      name: 'senderId',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.senderId'),
        verificationRequired: true
      }
    },
    {
      name: 'recipientId',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.recipientId'),
        verificationRequired: true
      }
    },
    {
      name: 'content',
      type: { primitive: 'string', encoding: 'utf8' },
      required: true,
      constraints: [
        { type: 'min', value: 1, message: 'Message content must not be empty' },
        { type: 'max', value: 10000, message: 'Message content must be less than 10000 characters' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('message.content'),
        verificationRequired: true
      }
    },
    {
      name: 'messageType',
      type: { primitive: 'string', size: 50 },
      required: true,
      constraints: [
        { type: 'enum', value: ['text', 'image', 'file', 'system'], message: 'Invalid message type' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('message.messageType'),
        verificationRequired: false
      }
    },
    {
      name: 'createdAt',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.createdAt'),
        verificationRequired: false
      }
    },
    {
      name: 'readAt',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.readAt'),
        verificationRequired: false
      }
    },
    {
      name: 'isEncrypted',
      type: { primitive: 'boolean' },
      required: true,
      defaultValue: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.isEncrypted'),
        verificationRequired: false
      }
    },
    {
      name: 'attachments',
      type: { primitive: 'string', encoding: 'utf8' },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('message.attachments'),
        verificationRequired: false
      }
    }
  ],
  constraints: [
    {
      type: 'unique',
      fields: ['id'],
      holographicWeight: 1.0
    },
    {
      type: 'foreign-key',
      fields: ['senderId'],
      reference: { schema: 'user_profile', field: 'id' },
      holographicWeight: 0.8
    },
    {
      type: 'foreign-key',
      fields: ['recipientId'],
      reference: { schema: 'user_profile', field: 'id' },
      holographicWeight: 0.8
    },
    {
      type: 'holographic-integrity',
      fields: ['id', 'senderId', 'recipientId', 'content'],
      holographicWeight: 0.9
    }
  ],
  indexes: [
    {
      name: 'message_id_index',
      fields: ['id'],
      type: 'holographic',
      unique: true,
      performance: { cacheSize: 1000, compressionLevel: 0 }
    },
    {
      name: 'message_sender_index',
      fields: ['senderId'],
      type: 'btree',
      unique: false,
      performance: { cacheSize: 500, compressionLevel: 1 }
    },
    {
      name: 'message_recipient_index',
      fields: ['recipientId'],
      type: 'btree',
      unique: false,
      performance: { cacheSize: 500, compressionLevel: 1 }
    },
    {
      name: 'message_conversation_index',
      fields: ['senderId', 'recipientId', 'createdAt'],
      type: 'composite',
      unique: false,
      performance: { cacheSize: 300, compressionLevel: 1 }
    },
    {
      name: 'message_unread_index',
      fields: ['recipientId', 'readAt'],
      type: 'composite',
      unique: false,
      performance: { cacheSize: 200, compressionLevel: 2 }
    }
  ],
  holographicProperties: {
    fingerprint: generateHolographicFingerprint('message_schema'),
    verificationLevel: 'maximum',
    integrityChecks: ['field_validation', 'constraint_checking', 'holographic_verification', 'foreign_key_validation', 'content_encryption_check']
  },
  performance: {
    compressionEnabled: true,
    cacheStrategy: 'lru',
    memoryLayout: 'packed'
  }
};

/**
 * Performance Metrics Schema
 */
export const PerformanceMetricsSchema: ADLSchema = {
  id: 'performance_metrics',
  name: 'Performance Metrics',
  version: '1.0.0',
  fields: [
    {
      name: 'id',
      type: { primitive: 'string', size: 36 },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.id'),
        verificationRequired: true
      }
    },
    {
      name: 'operationType',
      type: { primitive: 'string', size: 100 },
      required: true,
      constraints: [
        { type: 'enum', value: ['read', 'write', 'update', 'delete', 'query'], message: 'Invalid operation type' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.operationType'),
        verificationRequired: false
      }
    },
    {
      name: 'duration',
      type: { primitive: 'number', precision: 3 },
      required: true,
      constraints: [
        { type: 'min', value: 0, message: 'Duration must be non-negative' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.duration'),
        verificationRequired: false
      }
    },
    {
      name: 'throughput',
      type: { primitive: 'number', precision: 2 },
      required: true,
      constraints: [
        { type: 'min', value: 0, message: 'Throughput must be non-negative' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.throughput'),
        verificationRequired: false
      }
    },
    {
      name: 'timestamp',
      type: { primitive: 'timestamp', format: 'iso8601' },
      required: true,
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.timestamp'),
        verificationRequired: false
      }
    },
    {
      name: 'resourceUsage',
      type: { primitive: 'string', encoding: 'utf8' },
      required: false,
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.resourceUsage'),
        verificationRequired: false
      }
    },
    {
      name: 'errorCount',
      type: { primitive: 'number', precision: 0 },
      required: true,
      defaultValue: 0,
      constraints: [
        { type: 'min', value: 0, message: 'Error count must be non-negative' }
      ],
      holographic: {
        fingerprint: generateHolographicFingerprint('performance_metrics.errorCount'),
        verificationRequired: false
      }
    }
  ],
  constraints: [
    {
      type: 'unique',
      fields: ['id'],
      holographicWeight: 1.0
    },
    {
      type: 'holographic-integrity',
      fields: ['id', 'operationType', 'duration', 'throughput'],
      holographicWeight: 0.7
    }
  ],
  indexes: [
    {
      name: 'performance_metrics_id_index',
      fields: ['id'],
      type: 'holographic',
      unique: true,
      performance: { cacheSize: 1000, compressionLevel: 0 }
    },
    {
      name: 'performance_metrics_operation_index',
      fields: ['operationType'],
      type: 'hash',
      unique: false,
      performance: { cacheSize: 100, compressionLevel: 2 }
    },
    {
      name: 'performance_metrics_timestamp_index',
      fields: ['timestamp'],
      type: 'btree',
      unique: false,
      performance: { cacheSize: 200, compressionLevel: 1 }
    },
    {
      name: 'performance_metrics_composite_index',
      fields: ['operationType', 'timestamp'],
      type: 'composite',
      unique: false,
      performance: { cacheSize: 300, compressionLevel: 1 }
    }
  ],
  holographicProperties: {
    fingerprint: generateHolographicFingerprint('performance_metrics_schema'),
    verificationLevel: 'enhanced',
    integrityChecks: ['field_validation', 'constraint_checking', 'holographic_verification', 'performance_data_validation']
  },
  performance: {
    compressionEnabled: true,
    cacheStrategy: 'fifo',
    memoryLayout: 'sparse'
  }
};

/**
 * All available schemas
 */
export const AvailableSchemas: ADLSchema[] = [
  UserProfileSchema,
  DocumentSchema,
  MessageSchema,
  PerformanceMetricsSchema
];

/**
 * Get schema by ID
 */
export function getSchemaById(schemaId: string): ADLSchema | null {
  return AvailableSchemas.find(schema => schema.id === schemaId) || null;
}

/**
 * Get all schema IDs
 */
export function getAllSchemaIds(): string[] {
  return AvailableSchemas.map(schema => schema.id);
}

/**
 * Validate schema compatibility
 */
export function validateSchemaCompatibility(schema1: ADLSchema, schema2: ADLSchema): boolean {
  // Check if schemas have compatible field types
  const fields1 = new Map(schema1.fields.map(f => [f.name, f.type]));
  const fields2 = new Map(schema2.fields.map(f => [f.name, f.type]));
  
  for (const [name, type1] of fields1) {
    const type2 = fields2.get(name);
    if (type2 && type1.primitive !== type2.primitive) {
      return false;
    }
  }
  
  return true;
}

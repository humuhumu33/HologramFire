/**
 * Enhanced Storage Manager
 * 
 * Extends storage systems with database integration, cross-modal storage dependencies,
 * and unified storage management as part of the UOR framework.
 */

import { ccmHash } from "../../crypto/ccm/CCMHash";
import { Metrics } from "../../monitoring/metrics/Metrics";

export interface StorageSystem {
  uorId: string;
  name: string;
  type: 'database' | 'filesystem' | 'object_storage' | 'block_storage' | 'cache' | 'queue' | 'search';
  provider: 'aws' | 'gcp' | 'azure' | 'local' | 'kubernetes' | 'docker';
  properties: {
    endpoint: string;
    credentials?: Record<string, any>;
    region?: string;
    availabilityZone?: string;
    encryption: boolean;
    compression: boolean;
    replication: boolean;
    backup: boolean;
    versioning: boolean;
  };
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    version: string;
    status: 'active' | 'inactive' | 'maintenance' | 'failed';
    capacity: StorageCapacity;
    utilization: StorageUtilization;
    performance: StoragePerformance;
  };
}

export interface StorageCapacity {
  total: number; // bytes
  used: number; // bytes
  available: number; // bytes
  reserved: number; // bytes
  quota?: number; // bytes
}

export interface StorageUtilization {
  readOps: number; // operations per second
  writeOps: number; // operations per second
  readBytes: number; // bytes per second
  writeBytes: number; // bytes per second
  connections: number;
  cacheHitRate: number; // percentage
}

export interface StoragePerformance {
  readLatency: number; // milliseconds
  writeLatency: number; // milliseconds
  throughput: number; // bytes per second
  iops: number; // input/output operations per second
  errorRate: number; // percentage
}

export interface StorageVolume {
  uorId: string;
  storageSystemUorId: string;
  name: string;
  type: 'persistent' | 'ephemeral' | 'shared' | 'local';
  size: number; // bytes
  mountPoint?: string;
  filesystem?: string;
  properties: {
    accessMode: 'read_write_once' | 'read_only_many' | 'read_write_many';
    reclaimPolicy: 'retain' | 'recycle' | 'delete';
    storageClass?: string;
    volumeMode: 'filesystem' | 'block';
  };
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    status: 'available' | 'bound' | 'released' | 'failed' | 'pending';
    attachedTo?: string[];
    snapshots: StorageSnapshot[];
  };
}

export interface StorageSnapshot {
  uorId: string;
  volumeUorId: string;
  name: string;
  size: number; // bytes
  timestamp: string;
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    status: 'creating' | 'completed' | 'failed' | 'deleted';
    incremental: boolean;
    parentSnapshot?: string;
  };
}

export interface DatabaseStorage {
  uorId: string;
  storageSystemUorId: string;
  name: string;
  engine: 'postgresql' | 'mysql' | 'mongodb' | 'redis' | 'elasticsearch' | 'cassandra' | 'dynamodb';
  version: string;
  properties: {
    host: string;
    port: number;
    database: string;
    username?: string;
    ssl: boolean;
    connectionString: string;
    poolSize: number;
    timeout: number;
  };
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    status: 'running' | 'stopped' | 'maintenance' | 'failed';
    schemas: DatabaseSchema[];
    tables: DatabaseTable[];
    indexes: DatabaseIndex[];
    connections: DatabaseConnection[];
  };
}

export interface DatabaseSchema {
  uorId: string;
  databaseUorId: string;
  name: string;
  owner: string;
  tables: string[];
  views: string[];
  procedures: string[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    size: number;
    permissions: string[];
  };
}

export interface DatabaseTable {
  uorId: string;
  schemaUorId: string;
  name: string;
  columns: DatabaseColumn[];
  rows: number;
  size: number; // bytes
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    lastAccessed: string;
    indexes: string[];
    constraints: string[];
  };
}

export interface DatabaseColumn {
  name: string;
  type: string;
  nullable: boolean;
  defaultValue?: any;
  primaryKey: boolean;
  foreignKey?: {
    referencedTable: string;
    referencedColumn: string;
  };
  index: boolean;
  unique: boolean;
}

export interface DatabaseIndex {
  uorId: string;
  tableUorId: string;
  name: string;
  columns: string[];
  type: 'btree' | 'hash' | 'gin' | 'gist' | 'brin';
  unique: boolean;
  partial: boolean;
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastUsed: string;
    size: number;
    usage: number; // percentage
  };
}

export interface DatabaseConnection {
  uorId: string;
  databaseUorId: string;
  applicationUorId: string;
  properties: {
    host: string;
    port: number;
    database: string;
    username: string;
    ssl: boolean;
    poolSize: number;
    timeout: number;
  };
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastActivity: string;
    status: 'active' | 'idle' | 'closed' | 'error';
    queriesExecuted: number;
    bytesTransferred: number;
    averageLatency: number;
  };
}

export interface StorageDependency {
  uorId: string;
  sourceUorId: string; // Application or service
  targetUorId: string; // Storage system or database
  dependencyType: 'reads' | 'writes' | 'reads_writes' | 'backup' | 'replication' | 'cache';
  holographicFingerprint: string;
  witnessSignature: string;
  metadata: {
    createdAt: string;
    lastUsed: string;
    frequency: number;
    criticality: 'low' | 'medium' | 'high' | 'critical';
    dataClassification: 'public' | 'internal' | 'confidential' | 'restricted';
    retention: number; // days
  };
}

export interface StorageBackup {
  uorId: string;
  sourceUorId: string; // Source storage system
  targetUorId: string; // Backup storage system
  name: string;
  type: 'full' | 'incremental' | 'differential';
  size: number; // bytes
  holographicFingerprint: string;
  witnessSignature: string;
  metadata: {
    createdAt: string;
    completedAt?: string;
    status: 'pending' | 'in_progress' | 'completed' | 'failed' | 'expired';
    retention: number; // days
    compression: boolean;
    encryption: boolean;
    checksum: string;
  };
}

export interface StorageReplication {
  uorId: string;
  sourceUorId: string; // Source storage system
  targetUorId: string; // Target storage system
  type: 'synchronous' | 'asynchronous' | 'snapshot';
  holographicFingerprint: string;
  witnessSignature: string;
  metadata: {
    createdAt: string;
    lastSync: string;
    status: 'active' | 'paused' | 'failed' | 'stopped';
    lag: number; // milliseconds
    throughput: number; // bytes per second
    errorRate: number; // percentage
  };
}

export interface EnhancedStorageManagerConfig {
  enableDatabaseIntegration: boolean;
  enableBackupManagement: boolean;
  enableReplicationManagement: boolean;
  enablePerformanceMonitoring: boolean;
  enableDependencyTracking: boolean;
  monitoringIntervalMs: number;
  backupIntervalMs: number;
  replicationCheckIntervalMs: number;
  retentionDays: number;
  maxConnectionsPerDatabase: number;
}

export class EnhancedStorageManager {
  private config: EnhancedStorageManagerConfig;
  private metrics: Metrics;
  private storageSystems: Map<string, StorageSystem> = new Map();
  private volumes: Map<string, StorageVolume> = new Map();
  private databases: Map<string, DatabaseStorage> = new Map();
  private dependencies: Map<string, StorageDependency> = new Map();
  private backups: Map<string, StorageBackup> = new Map();
  private replications: Map<string, StorageReplication> = new Map();
  private monitoringTimer: NodeJS.Timeout | null = null;
  private backupTimer: NodeJS.Timeout | null = null;
  private replicationTimer: NodeJS.Timeout | null = null;

  constructor(config: Partial<EnhancedStorageManagerConfig> = {}, metrics: Metrics) {
    this.config = {
      enableDatabaseIntegration: config.enableDatabaseIntegration !== false,
      enableBackupManagement: config.enableBackupManagement !== false,
      enableReplicationManagement: config.enableReplicationManagement !== false,
      enablePerformanceMonitoring: config.enablePerformanceMonitoring !== false,
      enableDependencyTracking: config.enableDependencyTracking !== false,
      monitoringIntervalMs: config.monitoringIntervalMs || 30000,
      backupIntervalMs: config.backupIntervalMs || 3600000,
      replicationCheckIntervalMs: config.replicationCheckIntervalMs || 60000,
      retentionDays: config.retentionDays || 30,
      maxConnectionsPerDatabase: config.maxConnectionsPerDatabase || 100,
      ...config
    };
    this.metrics = metrics;
  }

  /**
   * Register storage system
   */
  async registerStorageSystem(
    name: string,
    type: StorageSystem['type'],
    provider: StorageSystem['provider'],
    properties: Partial<StorageSystem['properties']> = {},
    metadata: Partial<StorageSystem['metadata']> = {}
  ): Promise<StorageSystem> {
    const uorId = this.generateUORId('storage_system', name, type);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, type, properties });

    const storageSystem: StorageSystem = {
      uorId,
      name,
      type,
      provider,
      properties: {
        endpoint: 'localhost',
        encryption: false,
        compression: false,
        replication: false,
        backup: false,
        versioning: false,
        ...properties
      },
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        version: '1.0.0',
        status: 'active',
        capacity: {
          total: 1000000000000, // 1 TB
          used: 0,
          available: 1000000000000,
          reserved: 0
        },
        utilization: {
          readOps: 0,
          writeOps: 0,
          readBytes: 0,
          writeBytes: 0,
          connections: 0,
          cacheHitRate: 0
        },
        performance: {
          readLatency: 1,
          writeLatency: 1,
          throughput: 0,
          iops: 0,
          errorRate: 0
        },
        ...metadata
      }
    };

    this.storageSystems.set(uorId, storageSystem);
    this.metrics.inc("storage_systems_registered");

    return storageSystem;
  }

  /**
   * Create storage volume
   */
  async createVolume(
    storageSystemUorId: string,
    name: string,
    size: number,
    type: StorageVolume['type'] = 'persistent',
    properties: Partial<StorageVolume['properties']> = {}
  ): Promise<StorageVolume> {
    const storageSystem = this.storageSystems.get(storageSystemUorId);
    if (!storageSystem) {
      throw new Error(`Storage system ${storageSystemUorId} not found`);
    }

    const uorId = this.generateUORId('volume', storageSystemUorId, name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, size, type });

    const volume: StorageVolume = {
      uorId,
      storageSystemUorId,
      name,
      type,
      size,
      properties: {
        accessMode: 'read_write_once',
        reclaimPolicy: 'retain',
        volumeMode: 'filesystem',
        ...properties
      },
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        status: 'available',
        attachedTo: [],
        snapshots: []
      }
    };

    this.volumes.set(uorId, volume);
    this.metrics.inc("storage_volumes_created");

    return volume;
  }

  /**
   * Register database storage
   */
  async registerDatabase(
    storageSystemUorId: string,
    name: string,
    engine: DatabaseStorage['engine'],
    version: string,
    properties: Partial<DatabaseStorage['properties']> = {}
  ): Promise<DatabaseStorage> {
    if (!this.config.enableDatabaseIntegration) {
      throw new Error("Database integration is not enabled");
    }

    const storageSystem = this.storageSystems.get(storageSystemUorId);
    if (!storageSystem) {
      throw new Error(`Storage system ${storageSystemUorId} not found`);
    }

    const uorId = this.generateUORId('database', storageSystemUorId, name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, engine, version });

    const database: DatabaseStorage = {
      uorId,
      storageSystemUorId,
      name,
      engine,
      version,
      properties: {
        host: 'localhost',
        port: this.getDefaultPort(engine),
        database: name,
        ssl: false,
        connectionString: '',
        poolSize: 10,
        timeout: 30000,
        ...properties
      },
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        status: 'running',
        schemas: [],
        tables: [],
        indexes: [],
        connections: []
      }
    };

    this.databases.set(uorId, database);
    this.metrics.inc("databases_registered");

    return database;
  }

  /**
   * Create database schema
   */
  async createDatabaseSchema(
    databaseUorId: string,
    name: string,
    owner: string = 'postgres'
  ): Promise<DatabaseSchema> {
    const database = this.databases.get(databaseUorId);
    if (!database) {
      throw new Error(`Database ${databaseUorId} not found`);
    }

    const uorId = this.generateUORId('schema', databaseUorId, name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, owner });

    const schema: DatabaseSchema = {
      uorId,
      databaseUorId,
      name,
      owner,
      tables: [],
      views: [],
      procedures: [],
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        size: 0,
        permissions: ['SELECT', 'INSERT', 'UPDATE', 'DELETE']
      }
    };

    database.metadata.schemas.push(schema);
    this.databases.set(databaseUorId, database);
    this.metrics.inc("database_schemas_created");

    return schema;
  }

  /**
   * Create database table
   */
  async createDatabaseTable(
    schemaUorId: string,
    name: string,
    columns: DatabaseColumn[]
  ): Promise<DatabaseTable> {
    const uorId = this.generateUORId('table', schemaUorId, name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, columns });

    const table: DatabaseTable = {
      uorId,
      schemaUorId,
      name,
      columns,
      rows: 0,
      size: 0,
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        lastAccessed: new Date().toISOString(),
        indexes: [],
        constraints: []
      }
    };

    // Find and update the database
    for (const [databaseUorId, database] of this.databases) {
      const schema = database.metadata.schemas.find(s => s.uorId === schemaUorId);
      if (schema) {
        schema.tables.push(table.uorId);
        database.metadata.tables.push(table);
        this.databases.set(databaseUorId, database);
        break;
      }
    }

    this.metrics.inc("database_tables_created");
    return table;
  }

  /**
   * Track storage dependency
   */
  async trackDependency(
    sourceUorId: string,
    targetUorId: string,
    dependencyType: StorageDependency['dependencyType'],
    metadata: Partial<StorageDependency['metadata']> = {}
  ): Promise<StorageDependency> {
    const uorId = this.generateUORId('storage_dependency', sourceUorId, targetUorId);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { sourceUorId, targetUorId, dependencyType });
    const witnessSignature = await this.generateWitnessSignature(uorId, { sourceUorId, targetUorId, dependencyType });

    const dependency: StorageDependency = {
      uorId,
      sourceUorId,
      targetUorId,
      dependencyType,
      holographicFingerprint,
      witnessSignature,
      metadata: {
        createdAt: new Date().toISOString(),
        lastUsed: new Date().toISOString(),
        frequency: 1,
        criticality: 'medium',
        dataClassification: 'internal',
        retention: 30,
        ...metadata
      }
    };

    this.dependencies.set(uorId, dependency);
    this.metrics.inc("storage_dependencies_tracked");

    return dependency;
  }

  /**
   * Create backup
   */
  async createBackup(
    sourceUorId: string,
    targetUorId: string,
    name: string,
    type: StorageBackup['type'] = 'full',
    metadata: Partial<StorageBackup['metadata']> = {}
  ): Promise<StorageBackup> {
    if (!this.config.enableBackupManagement) {
      throw new Error("Backup management is not enabled");
    }

    const uorId = this.generateUORId('backup', sourceUorId, name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { sourceUorId, targetUorId, name });
    const witnessSignature = await this.generateWitnessSignature(uorId, { sourceUorId, targetUorId, name });

    const backup: StorageBackup = {
      uorId,
      sourceUorId,
      targetUorId,
      name,
      type,
      size: 0, // Will be updated when backup completes
      holographicFingerprint,
      witnessSignature,
      metadata: {
        createdAt: new Date().toISOString(),
        status: 'pending',
        retention: 30,
        compression: true,
        encryption: true,
        checksum: '',
        ...metadata
      }
    };

    this.backups.set(uorId, backup);
    this.metrics.inc("storage_backups_created");

    // Simulate backup process
    await this.simulateBackup(backup);

    return backup;
  }

  /**
   * Simulate backup process
   */
  private async simulateBackup(backup: StorageBackup): Promise<void> {
    backup.metadata.status = 'in_progress';
    this.backups.set(backup.uorId, backup);

    // Simulate backup time
    await new Promise(resolve => setTimeout(resolve, 2000));

    // Update backup status
    backup.metadata.status = 'completed';
    backup.metadata.completedAt = new Date().toISOString();
    backup.size = Math.floor(Math.random() * 1000000000); // Random size up to 1GB
    backup.metadata.checksum = ccmHash(backup.name + backup.size, "backup_checksum");
    this.backups.set(backup.uorId, backup);

    this.metrics.inc("storage_backups_completed");
  }

  /**
   * Create replication
   */
  async createReplication(
    sourceUorId: string,
    targetUorId: string,
    type: StorageReplication['type'] = 'asynchronous'
  ): Promise<StorageReplication> {
    if (!this.config.enableReplicationManagement) {
      throw new Error("Replication management is not enabled");
    }

    const uorId = this.generateUORId('replication', sourceUorId, targetUorId);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { sourceUorId, targetUorId, type });
    const witnessSignature = await this.generateWitnessSignature(uorId, { sourceUorId, targetUorId, type });

    const replication: StorageReplication = {
      uorId,
      sourceUorId,
      targetUorId,
      type,
      holographicFingerprint,
      witnessSignature,
      metadata: {
        createdAt: new Date().toISOString(),
        lastSync: new Date().toISOString(),
        status: 'active',
        lag: 0,
        throughput: 0,
        errorRate: 0
      }
    };

    this.replications.set(uorId, replication);
    this.metrics.inc("storage_replications_created");

    return replication;
  }

  /**
   * Monitor storage performance
   */
  async monitorStoragePerformance(storageSystemUorId: string): Promise<void> {
    const storageSystem = this.storageSystems.get(storageSystemUorId);
    if (!storageSystem) {
      throw new Error(`Storage system ${storageSystemUorId} not found`);
    }

    // Mock performance monitoring
    const utilization = storageSystem.metadata.utilization;
    const performance = storageSystem.metadata.performance;

    // Simulate some activity
    utilization.readOps += Math.floor(Math.random() * 100);
    utilization.writeOps += Math.floor(Math.random() * 50);
    utilization.readBytes += Math.floor(Math.random() * 1000000);
    utilization.writeBytes += Math.floor(Math.random() * 500000);
    utilization.connections = Math.floor(Math.random() * 100);
    utilization.cacheHitRate = Math.random() * 100;

    performance.readLatency = Math.random() * 10 + 1;
    performance.writeLatency = Math.random() * 15 + 2;
    performance.throughput = Math.random() * 1000000000;
    performance.iops = Math.floor(Math.random() * 10000);
    performance.errorRate = Math.random() * 0.1;

    this.storageSystems.set(storageSystemUorId, storageSystem);
    this.metrics.inc("storage_performance_monitored");
  }

  /**
   * Start monitoring
   */
  startMonitoring(): void {
    if (this.config.enablePerformanceMonitoring && !this.monitoringTimer) {
      this.monitoringTimer = setInterval(async () => {
        await this.performPeriodicMonitoring();
      }, this.config.monitoringIntervalMs);
    }

    if (this.config.enableBackupManagement && !this.backupTimer) {
      this.backupTimer = setInterval(async () => {
        await this.performPeriodicBackups();
      }, this.config.backupIntervalMs);
    }

    if (this.config.enableReplicationManagement && !this.replicationTimer) {
      this.replicationTimer = setInterval(async () => {
        await this.performPeriodicReplicationChecks();
      }, this.config.replicationCheckIntervalMs);
    }
  }

  /**
   * Stop monitoring
   */
  stopMonitoring(): void {
    if (this.monitoringTimer) {
      clearInterval(this.monitoringTimer);
      this.monitoringTimer = null;
    }

    if (this.backupTimer) {
      clearInterval(this.backupTimer);
      this.backupTimer = null;
    }

    if (this.replicationTimer) {
      clearInterval(this.replicationTimer);
      this.replicationTimer = null;
    }
  }

  /**
   * Perform periodic monitoring
   */
  private async performPeriodicMonitoring(): Promise<void> {
    for (const [uorId, storageSystem] of this.storageSystems) {
      try {
        await this.monitorStoragePerformance(uorId);
      } catch (error) {
        this.metrics.inc("periodic_monitoring_errors");
        console.error(`Periodic monitoring failed for storage system ${storageSystem.name}:`, error);
      }
    }
  }

  /**
   * Perform periodic backups
   */
  private async performPeriodicBackups(): Promise<void> {
    for (const [uorId, storageSystem] of this.storageSystems) {
      if (storageSystem.properties.backup) {
        try {
          const backupName = `auto-backup-${Date.now()}`;
          await this.createBackup(uorId, uorId, backupName, 'incremental');
        } catch (error) {
          this.metrics.inc("periodic_backup_errors");
          console.error(`Periodic backup failed for storage system ${storageSystem.name}:`, error);
        }
      }
    }
  }

  /**
   * Perform periodic replication checks
   */
  private async performPeriodicReplicationChecks(): Promise<void> {
    for (const [uorId, replication] of this.replications) {
      try {
        // Mock replication health check
        replication.metadata.lastSync = new Date().toISOString();
        replication.metadata.lag = Math.random() * 100;
        replication.metadata.throughput = Math.random() * 100000000;
        replication.metadata.errorRate = Math.random() * 0.01;

        this.replications.set(uorId, replication);
        this.metrics.inc("replication_health_checks");
      } catch (error) {
        this.metrics.inc("replication_check_errors");
        console.error(`Replication check failed for ${replication.uorId}:`, error);
      }
    }
  }

  /**
   * Get all storage systems
   */
  getStorageSystems(): StorageSystem[] {
    return Array.from(this.storageSystems.values());
  }

  /**
   * Get all volumes
   */
  getVolumes(): StorageVolume[] {
    return Array.from(this.volumes.values());
  }

  /**
   * Get all databases
   */
  getDatabases(): DatabaseStorage[] {
    return Array.from(this.databases.values());
  }

  /**
   * Get all dependencies
   */
  getDependencies(): StorageDependency[] {
    return Array.from(this.dependencies.values());
  }

  /**
   * Get all backups
   */
  getBackups(): StorageBackup[] {
    return Array.from(this.backups.values());
  }

  /**
   * Get all replications
   */
  getReplications(): StorageReplication[] {
    return Array.from(this.replications.values());
  }

  /**
   * Get default port for database engine
   */
  private getDefaultPort(engine: DatabaseStorage['engine']): number {
    const ports: Record<DatabaseStorage['engine'], number> = {
      postgresql: 5432,
      mysql: 3306,
      mongodb: 27017,
      redis: 6379,
      elasticsearch: 9200,
      cassandra: 9042,
      dynamodb: 8000
    };
    return ports[engine];
  }

  /**
   * Generate UOR-ID
   */
  private generateUORId(type: string, ...parts: string[]): string {
    const content = `${type}:${parts.join(':')}`;
    return `atlas-12288/infrastructure/storage/${ccmHash(content, "uor_id")}`;
  }

  /**
   * Generate holographic fingerprint
   */
  private generateHolographicFingerprint(uorId: string, data: any): string {
    return ccmHash(JSON.stringify({ uorId, data }), "holographic_fingerprint");
  }

  /**
   * Generate witness signature
   */
  private async generateWitnessSignature(uorId: string, data: any): Promise<string> {
    return ccmHash(JSON.stringify({ uorId, data, timestamp: Date.now() }), "witness_signature");
  }

  /**
   * Cleanup old data
   */
  async cleanup(): Promise<void> {
    const cutoffDate = new Date(Date.now() - (this.config.retentionDays * 24 * 60 * 60 * 1000));
    
    // Clean up old backups
    for (const [uorId, backup] of this.backups) {
      if (new Date(backup.metadata.createdAt) < cutoffDate) {
        this.backups.delete(uorId);
        this.metrics.inc("storage_backups_cleaned");
      }
    }

    // Clean up old dependencies
    for (const [uorId, dependency] of this.dependencies) {
      if (new Date(dependency.metadata.createdAt) < cutoffDate) {
        this.dependencies.delete(uorId);
        this.metrics.inc("storage_dependencies_cleaned");
      }
    }
  }
}

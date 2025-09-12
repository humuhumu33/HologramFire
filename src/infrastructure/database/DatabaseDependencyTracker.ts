/**
 * Database Dependency Tracker
 * 
 * Tracks database dependencies, connections, and relationships across the infrastructure
 * as part of the UOR framework for single-context content resolution.
 */

import { ccmHash } from "../../crypto/ccm/CCMHash";
import { Metrics } from "../../monitoring/metrics/Metrics";

export interface DatabaseConnection {
  uorId: string;
  name: string;
  type: 'postgresql' | 'mysql' | 'mongodb' | 'redis' | 'elasticsearch' | 'cassandra' | 'dynamodb';
  host: string;
  port: number;
  database: string;
  username?: string;
  ssl: boolean;
  connectionString: string;
  holographicFingerprint: string;
  metadata: {
    version: string;
    driver: string;
    poolSize: number;
    timeout: number;
    createdAt: string;
    lastAccessed: string;
  };
}

export interface DatabaseDependency {
  uorId: string;
  sourceUorId: string; // Application or service UOR-ID
  targetUorId: string; // Database UOR-ID
  dependencyType: 'read' | 'write' | 'read_write' | 'admin';
  tables: string[];
  schemas: string[];
  operations: string[];
  holographicFingerprint: string;
  witnessSignature: string;
  metadata: {
    createdAt: string;
    lastUsed: string;
    frequency: number;
    criticality: 'low' | 'medium' | 'high' | 'critical';
    dataClassification: 'public' | 'internal' | 'confidential' | 'restricted';
  };
}

export interface DatabaseSchema {
  uorId: string;
  databaseUorId: string;
  name: string;
  tables: DatabaseTable[];
  views: DatabaseView[];
  procedures: DatabaseProcedure[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    version: string;
    owner: string;
  };
}

export interface DatabaseTable {
  uorId: string;
  schemaUorId: string;
  name: string;
  columns: DatabaseColumn[];
  indexes: DatabaseIndex[];
  constraints: DatabaseConstraint[];
  holographicFingerprint: string;
  metadata: {
    rowCount: number;
    sizeBytes: number;
    createdAt: string;
    lastModified: string;
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
}

export interface DatabaseIndex {
  name: string;
  columns: string[];
  unique: boolean;
  type: 'btree' | 'hash' | 'gin' | 'gist';
}

export interface DatabaseConstraint {
  name: string;
  type: 'primary_key' | 'foreign_key' | 'unique' | 'check';
  definition: string;
}

export interface DatabaseView {
  uorId: string;
  schemaUorId: string;
  name: string;
  definition: string;
  holographicFingerprint: string;
}

export interface DatabaseProcedure {
  uorId: string;
  schemaUorId: string;
  name: string;
  parameters: DatabaseParameter[];
  returnType?: string;
  definition: string;
  holographicFingerprint: string;
}

export interface DatabaseParameter {
  name: string;
  type: string;
  direction: 'in' | 'out' | 'inout';
  defaultValue?: any;
}

export interface DatabaseDependencyGraph {
  uorId: string;
  nodes: DatabaseNode[];
  edges: DatabaseEdge[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastUpdated: string;
    totalNodes: number;
    totalEdges: number;
  };
}

export interface DatabaseNode {
  uorId: string;
  type: 'database' | 'schema' | 'table' | 'view' | 'procedure' | 'application';
  name: string;
  properties: Record<string, any>;
}

export interface DatabaseEdge {
  sourceUorId: string;
  targetUorId: string;
  relationship: 'depends_on' | 'references' | 'uses' | 'owns';
  weight: number;
  properties: Record<string, any>;
}

export interface DatabaseDependencyTrackerConfig {
  enableRealTimeTracking: boolean;
  enableSchemaDiscovery: boolean;
  enablePerformanceMonitoring: boolean;
  enableSecurityScanning: boolean;
  maxConnectionsPerDatabase: number;
  discoveryIntervalMs: number;
  retentionDays: number;
}

export class DatabaseDependencyTracker {
  private config: DatabaseDependencyTrackerConfig;
  private metrics: Metrics;
  private connections: Map<string, DatabaseConnection> = new Map();
  private dependencies: Map<string, DatabaseDependency> = new Map();
  private schemas: Map<string, DatabaseSchema> = new Map();
  private dependencyGraph: DatabaseDependencyGraph | null = null;
  private discoveryTimer: NodeJS.Timeout | null = null;

  constructor(config: Partial<DatabaseDependencyTrackerConfig> = {}, metrics: Metrics) {
    this.config = {
      enableRealTimeTracking: config.enableRealTimeTracking !== false,
      enableSchemaDiscovery: config.enableSchemaDiscovery !== false,
      enablePerformanceMonitoring: config.enablePerformanceMonitoring !== false,
      enableSecurityScanning: config.enableSecurityScanning !== false,
      maxConnectionsPerDatabase: config.maxConnectionsPerDatabase || 10,
      discoveryIntervalMs: config.discoveryIntervalMs || 30000,
      retentionDays: config.retentionDays || 30,
      ...config
    };
    this.metrics = metrics;
  }

  /**
   * Register a database connection
   */
  async registerDatabaseConnection(connection: Omit<DatabaseConnection, 'uorId' | 'holographicFingerprint'>): Promise<DatabaseConnection> {
    const uorId = this.generateUORId('database', connection.name, connection.connectionString);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, connection);

    const fullConnection: DatabaseConnection = {
      ...connection,
      uorId,
      holographicFingerprint
    };

    this.connections.set(uorId, fullConnection);
    this.metrics.inc("database_connections_registered");

    // Start discovery if enabled
    if (this.config.enableSchemaDiscovery) {
      await this.discoverDatabaseSchema(fullConnection);
    }

    return fullConnection;
  }

  /**
   * Track a database dependency
   */
  async trackDependency(
    sourceUorId: string,
    targetUorId: string,
    dependencyType: DatabaseDependency['dependencyType'],
    tables: string[] = [],
    schemas: string[] = [],
    operations: string[] = []
  ): Promise<DatabaseDependency> {
    const uorId = this.generateUORId('dependency', sourceUorId, targetUorId);
    const witnessSignature = await this.generateWitnessSignature(uorId, { sourceUorId, targetUorId, dependencyType });

    const dependency: DatabaseDependency = {
      uorId,
      sourceUorId,
      targetUorId,
      dependencyType,
      tables,
      schemas,
      operations,
      holographicFingerprint: this.generateHolographicFingerprint(uorId, { sourceUorId, targetUorId }),
      witnessSignature,
      metadata: {
        createdAt: new Date().toISOString(),
        lastUsed: new Date().toISOString(),
        frequency: 1,
        criticality: this.assessCriticality(dependencyType, tables),
        dataClassification: this.assessDataClassification(tables)
      }
    };

    this.dependencies.set(uorId, dependency);
    this.metrics.inc("database_dependencies_tracked");

    // Update dependency graph
    await this.updateDependencyGraph();

    return dependency;
  }

  /**
   * Discover database schema
   */
  private async discoverDatabaseSchema(connection: DatabaseConnection): Promise<void> {
    try {
      // This would integrate with actual database drivers
      // For now, we'll create a mock schema discovery
      const schemaUorId = this.generateUORId('schema', connection.uorId, 'public');
      
      const schema: DatabaseSchema = {
        uorId: schemaUorId,
        databaseUorId: connection.uorId,
        name: 'public',
        tables: await this.discoverTables(connection, schemaUorId),
        views: await this.discoverViews(connection, schemaUorId),
        procedures: await this.discoverProcedures(connection, schemaUorId),
        holographicFingerprint: this.generateHolographicFingerprint(schemaUorId, { databaseUorId: connection.uorId }),
        metadata: {
          createdAt: new Date().toISOString(),
          lastModified: new Date().toISOString(),
          version: '1.0',
          owner: connection.username || 'unknown'
        }
      };

      this.schemas.set(schemaUorId, schema);
      this.metrics.inc("database_schemas_discovered");
    } catch (error) {
      this.metrics.inc("database_schema_discovery_errors");
      console.error(`Schema discovery failed for ${connection.name}:`, error);
    }
  }

  /**
   * Discover database tables
   */
  private async discoverTables(connection: DatabaseConnection, schemaUorId: string): Promise<DatabaseTable[]> {
    // Mock implementation - would use actual database introspection
    const mockTables: DatabaseTable[] = [
      {
        uorId: this.generateUORId('table', schemaUorId, 'users'),
        schemaUorId,
        name: 'users',
        columns: [
          { name: 'id', type: 'integer', nullable: false, primaryKey: true },
          { name: 'username', type: 'varchar(255)', nullable: false, primaryKey: false },
          { name: 'email', type: 'varchar(255)', nullable: false, primaryKey: false },
          { name: 'created_at', type: 'timestamp', nullable: false, primaryKey: false }
        ],
        indexes: [
          { name: 'idx_users_username', columns: ['username'], unique: true, type: 'btree' },
          { name: 'idx_users_email', columns: ['email'], unique: true, type: 'btree' }
        ],
        constraints: [
          { name: 'pk_users', type: 'primary_key', definition: 'PRIMARY KEY (id)' },
          { name: 'uk_users_username', type: 'unique', definition: 'UNIQUE (username)' }
        ],
        holographicFingerprint: this.generateHolographicFingerprint('users', { schemaUorId }),
        metadata: {
          rowCount: 1000,
          sizeBytes: 1024000,
          createdAt: new Date().toISOString(),
          lastModified: new Date().toISOString()
        }
      }
    ];

    return mockTables;
  }

  /**
   * Discover database views
   */
  private async discoverViews(connection: DatabaseConnection, schemaUorId: string): Promise<DatabaseView[]> {
    // Mock implementation
    return [
      {
        uorId: this.generateUORId('view', schemaUorId, 'user_summary'),
        schemaUorId,
        name: 'user_summary',
        definition: 'SELECT id, username, email FROM users WHERE active = true',
        holographicFingerprint: this.generateHolographicFingerprint('user_summary', { schemaUorId })
      }
    ];
  }

  /**
   * Discover database procedures
   */
  private async discoverProcedures(connection: DatabaseConnection, schemaUorId: string): Promise<DatabaseProcedure[]> {
    // Mock implementation
    return [
      {
        uorId: this.generateUORId('procedure', schemaUorId, 'create_user'),
        schemaUorId,
        name: 'create_user',
        parameters: [
          { name: 'p_username', type: 'varchar', direction: 'in' },
          { name: 'p_email', type: 'varchar', direction: 'in' },
          { name: 'p_user_id', type: 'integer', direction: 'out' }
        ],
        returnType: 'void',
        definition: 'CREATE OR REPLACE FUNCTION create_user(p_username varchar, p_email varchar) RETURNS integer AS $$ ... $$',
        holographicFingerprint: this.generateHolographicFingerprint('create_user', { schemaUorId })
      }
    ];
  }

  /**
   * Update dependency graph
   */
  private async updateDependencyGraph(): Promise<void> {
    const nodes: DatabaseNode[] = [];
    const edges: DatabaseEdge[] = [];

    // Add database nodes
    for (const [uorId, connection] of this.connections) {
      nodes.push({
        uorId,
        type: 'database',
        name: connection.name,
        properties: {
          type: connection.type,
          host: connection.host,
          port: connection.port
        }
      });
    }

    // Add schema nodes
    for (const [uorId, schema] of this.schemas) {
      nodes.push({
        uorId,
        type: 'schema',
        name: schema.name,
        properties: {
          tableCount: schema.tables.length,
          viewCount: schema.views.length
        }
      });

      // Add schema-database edge
      edges.push({
        sourceUorId: uorId,
        targetUorId: schema.databaseUorId,
        relationship: 'owns',
        weight: 1.0,
        properties: {}
      });
    }

    // Add table nodes and edges
    for (const [schemaUorId, schema] of this.schemas) {
      for (const table of schema.tables) {
        nodes.push({
          uorId: table.uorId,
          type: 'table',
          name: table.name,
          properties: {
            rowCount: table.metadata.rowCount,
            columnCount: table.columns.length
          }
        });

        // Add table-schema edge
        edges.push({
          sourceUorId: table.uorId,
          targetUorId: schemaUorId,
          relationship: 'owns',
          weight: 1.0,
          properties: {}
        });
      }
    }

    // Add dependency edges
    for (const [uorId, dependency] of this.dependencies) {
      edges.push({
        sourceUorId: dependency.sourceUorId,
        targetUorId: dependency.targetUorId,
        relationship: 'depends_on',
        weight: this.calculateDependencyWeight(dependency),
        properties: {
          type: dependency.dependencyType,
          tables: dependency.tables,
          criticality: dependency.metadata.criticality
        }
      });
    }

    this.dependencyGraph = {
      uorId: this.generateUORId('dependency_graph', 'infrastructure', 'databases'),
      nodes,
      edges,
      holographicFingerprint: this.generateHolographicFingerprint('dependency_graph', { nodeCount: nodes.length }),
      metadata: {
        createdAt: new Date().toISOString(),
        lastUpdated: new Date().toISOString(),
        totalNodes: nodes.length,
        totalEdges: edges.length
      }
    };

    this.metrics.inc("dependency_graphs_updated");
  }

  /**
   * Get dependency graph
   */
  getDependencyGraph(): DatabaseDependencyGraph | null {
    return this.dependencyGraph;
  }

  /**
   * Get all database connections
   */
  getConnections(): DatabaseConnection[] {
    return Array.from(this.connections.values());
  }

  /**
   * Get all dependencies
   */
  getDependencies(): DatabaseDependency[] {
    return Array.from(this.dependencies.values());
  }

  /**
   * Get dependencies for a specific source
   */
  getDependenciesForSource(sourceUorId: string): DatabaseDependency[] {
    return Array.from(this.dependencies.values()).filter(dep => dep.sourceUorId === sourceUorId);
  }

  /**
   * Get dependencies for a specific target
   */
  getDependenciesForTarget(targetUorId: string): DatabaseDependency[] {
    return Array.from(this.dependencies.values()).filter(dep => dep.targetUorId === targetUorId);
  }

  /**
   * Start real-time tracking
   */
  startTracking(): void {
    if (this.config.enableRealTimeTracking && !this.discoveryTimer) {
      this.discoveryTimer = setInterval(async () => {
        await this.performRealTimeDiscovery();
      }, this.config.discoveryIntervalMs);
    }
  }

  /**
   * Stop real-time tracking
   */
  stopTracking(): void {
    if (this.discoveryTimer) {
      clearInterval(this.discoveryTimer);
      this.discoveryTimer = null;
    }
  }

  /**
   * Perform real-time discovery
   */
  private async performRealTimeDiscovery(): Promise<void> {
    for (const [uorId, connection] of this.connections) {
      try {
        await this.discoverDatabaseSchema(connection);
        this.metrics.inc("real_time_discovery_success");
      } catch (error) {
        this.metrics.inc("real_time_discovery_errors");
        console.error(`Real-time discovery failed for ${connection.name}:`, error);
      }
    }
  }

  /**
   * Generate UOR-ID
   */
  private generateUORId(type: string, ...parts: string[]): string {
    const content = `${type}:${parts.join(':')}`;
    return `atlas-12288/infrastructure/database/${ccmHash(content, "uor_id")}`;
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
   * Assess dependency criticality
   */
  private assessCriticality(dependencyType: DatabaseDependency['dependencyType'], tables: string[]): DatabaseDependency['metadata']['criticality'] {
    if (dependencyType === 'admin' || tables.some(t => t.includes('user') || t.includes('auth'))) {
      return 'critical';
    }
    if (dependencyType === 'write' || tables.length > 5) {
      return 'high';
    }
    if (dependencyType === 'read_write') {
      return 'medium';
    }
    return 'low';
  }

  /**
   * Assess data classification
   */
  private assessDataClassification(tables: string[]): DatabaseDependency['metadata']['dataClassification'] {
    if (tables.some(t => t.includes('user') || t.includes('auth') || t.includes('password'))) {
      return 'restricted';
    }
    if (tables.some(t => t.includes('config') || t.includes('internal'))) {
      return 'confidential';
    }
    if (tables.some(t => t.includes('public') || t.includes('content'))) {
      return 'internal';
    }
    return 'public';
  }

  /**
   * Calculate dependency weight
   */
  private calculateDependencyWeight(dependency: DatabaseDependency): number {
    let weight = 1.0;
    
    // Adjust based on criticality
    switch (dependency.metadata.criticality) {
      case 'critical': weight *= 4.0; break;
      case 'high': weight *= 2.0; break;
      case 'medium': weight *= 1.5; break;
      case 'low': weight *= 1.0; break;
    }

    // Adjust based on dependency type
    switch (dependency.dependencyType) {
      case 'admin': weight *= 3.0; break;
      case 'write': weight *= 2.0; break;
      case 'read_write': weight *= 1.5; break;
      case 'read': weight *= 1.0; break;
    }

    // Adjust based on number of tables
    weight *= Math.min(1.0 + (dependency.tables.length * 0.1), 3.0);

    return weight;
  }

  /**
   * Cleanup old data
   */
  async cleanup(): Promise<void> {
    const cutoffDate = new Date(Date.now() - (this.config.retentionDays * 24 * 60 * 60 * 1000));
    
    // Remove old dependencies
    for (const [uorId, dependency] of this.dependencies) {
      if (new Date(dependency.metadata.createdAt) < cutoffDate) {
        this.dependencies.delete(uorId);
        this.metrics.inc("database_dependencies_cleaned");
      }
    }

    // Update dependency graph
    await this.updateDependencyGraph();
  }
}

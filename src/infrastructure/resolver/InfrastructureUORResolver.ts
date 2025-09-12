/**
 * Infrastructure UOR Resolver
 * 
 * Extends the UOR resolver to handle infrastructure components (database, networking, storage, IaC)
 * as part of the UOR framework for single-context content resolution.
 */

import { ccmHash } from "../../crypto/ccm/CCMHash";
import { Metrics } from "../../monitoring/metrics/Metrics";
import { DatabaseDependencyTracker } from "../database/DatabaseDependencyTracker";
import { InfrastructureAsCodeManager } from "../iac/InfrastructureAsCodeManager";
import { EnhancedNetworkManager } from "../network/EnhancedNetworkManager";
import { EnhancedStorageManager } from "../storage/EnhancedStorageManager";
import { InfrastructureOrchestrator } from "../orchestrator/InfrastructureOrchestrator";

export interface InfrastructureUORMapping {
  uorId: string;
  type: 'database' | 'network' | 'storage' | 'iac' | 'component' | 'deployment' | 'dependency';
  name: string;
  provider: string;
  region: string;
  environment: string;
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastAccessed: string;
    accessCount: number;
    tags: string[];
    properties: Record<string, any>;
  };
}

export interface InfrastructureResolutionResult {
  uorId: string;
  type: string;
  found: boolean;
  data: any;
  dependencies: string[];
  holographicFingerprint: string;
  metadata: {
    resolvedAt: string;
    resolutionTime: number;
    source: string;
    confidence: number;
  };
}

export interface InfrastructureQuery {
  type?: string;
  name?: string;
  provider?: string;
  region?: string;
  environment?: string;
  tags?: string[];
  properties?: Record<string, any>;
  limit?: number;
  offset?: number;
}

export interface InfrastructureDependencyGraph {
  uorId: string;
  rootUorId: string;
  nodes: InfrastructureGraphNode[];
  edges: InfrastructureGraphEdge[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastUpdated: string;
    totalNodes: number;
    totalEdges: number;
    maxDepth: number;
  };
}

export interface InfrastructureGraphNode {
  uorId: string;
  type: string;
  name: string;
  properties: Record<string, any>;
  metadata: {
    createdAt: string;
    lastModified: string;
    status: string;
    health: string;
  };
}

export interface InfrastructureGraphEdge {
  sourceUorId: string;
  targetUorId: string;
  relationship: string;
  weight: number;
  properties: Record<string, any>;
}

export interface InfrastructureUORResolverConfig {
  enableCaching: boolean;
  enableDependencyResolution: boolean;
  enableCrossModalQueries: boolean;
  enablePerformanceOptimization: boolean;
  cacheTimeoutMs: number;
  maxCacheSize: number;
  resolutionTimeoutMs: number;
  retentionDays: number;
}

export class InfrastructureUORResolver {
  private config: InfrastructureUORResolverConfig;
  private metrics: Metrics;
  private databaseTracker: DatabaseDependencyTracker;
  private iacManager: InfrastructureAsCodeManager;
  private networkManager: EnhancedNetworkManager;
  private storageManager: EnhancedStorageManager;
  private orchestrator: InfrastructureOrchestrator;
  private mappings: Map<string, InfrastructureUORMapping> = new Map();
  private cache: Map<string, InfrastructureResolutionResult> = new Map();
  private dependencyGraphs: Map<string, InfrastructureDependencyGraph> = new Map();

  constructor(
    config: Partial<InfrastructureUORResolverConfig> = {},
    metrics: Metrics,
    databaseTracker: DatabaseDependencyTracker,
    iacManager: InfrastructureAsCodeManager,
    networkManager: EnhancedNetworkManager,
    storageManager: EnhancedStorageManager,
    orchestrator: InfrastructureOrchestrator
  ) {
    this.config = {
      enableCaching: config.enableCaching !== false,
      enableDependencyResolution: config.enableDependencyResolution !== false,
      enableCrossModalQueries: config.enableCrossModalQueries !== false,
      enablePerformanceOptimization: config.enablePerformanceOptimization !== false,
      cacheTimeoutMs: config.cacheTimeoutMs || 300000, // 5 minutes
      maxCacheSize: config.maxCacheSize || 10000,
      resolutionTimeoutMs: config.resolutionTimeoutMs || 30000,
      retentionDays: config.retentionDays || 30,
      ...config
    };
    this.metrics = metrics;
    this.databaseTracker = databaseTracker;
    this.iacManager = iacManager;
    this.networkManager = networkManager;
    this.storageManager = storageManager;
    this.orchestrator = orchestrator;
  }

  /**
   * Resolve UOR-ID to infrastructure component
   */
  async resolveUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    const startTime = Date.now();

    // Check cache first
    if (this.config.enableCaching) {
      const cached = this.cache.get(uorId);
      if (cached && this.isCacheValid(cached)) {
        this.metrics.inc("infrastructure_uor_cache_hits");
        return cached;
      }
    }

    try {
      // Determine UOR type from ID
      const uorType = this.extractUORType(uorId);
      
      let result: InfrastructureResolutionResult;
      
      switch (uorType) {
        case 'database':
          result = await this.resolveDatabaseUOR(uorId);
          break;
        case 'network':
          result = await this.resolveNetworkUOR(uorId);
          break;
        case 'storage':
          result = await this.resolveStorageUOR(uorId);
          break;
        case 'iac':
          result = await this.resolveIaCUOR(uorId);
          break;
        case 'component':
          result = await this.resolveComponentUOR(uorId);
          break;
        case 'deployment':
          result = await this.resolveDeploymentUOR(uorId);
          break;
        case 'dependency':
          result = await this.resolveDependencyUOR(uorId);
          break;
        default:
          result = await this.resolveGenericUOR(uorId);
      }

      // Update metadata
      result.metadata.resolvedAt = new Date().toISOString();
      result.metadata.resolutionTime = Date.now() - startTime;
      result.metadata.confidence = this.calculateConfidence(result);

      // Cache result
      if (this.config.enableCaching) {
        this.cacheResult(uorId, result);
      }

      // Update mapping access
      this.updateMappingAccess(uorId);

      this.metrics.inc("infrastructure_uor_resolutions");
      return result;

    } catch (error) {
      this.metrics.inc("infrastructure_uor_resolution_errors");
      throw new Error(`Failed to resolve UOR ${uorId}: ${error}`);
    }
  }

  /**
   * Resolve database UOR
   */
  private async resolveDatabaseUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    // Try to find in database tracker
    const connections = this.databaseTracker.getConnections();
    const connection = connections.find(conn => conn.uorId === uorId);
    
    if (connection) {
      return {
        uorId,
        type: 'database_connection',
        found: true,
        data: connection,
        dependencies: this.databaseTracker.getDependenciesForTarget(uorId).map(dep => dep.sourceUorId),
        holographicFingerprint: connection.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'database_tracker',
          confidence: 1.0
        }
      };
    }

    // Try to find in storage manager databases
    const databases = this.storageManager.getDatabases();
    const database = databases.find(db => db.uorId === uorId);
    
    if (database) {
      return {
        uorId,
        type: 'database_storage',
        found: true,
        data: database,
        dependencies: this.storageManager.getDependencies().filter(dep => dep.targetUorId === uorId).map(dep => dep.sourceUorId),
        holographicFingerprint: database.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'storage_manager',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'database');
  }

  /**
   * Resolve network UOR
   */
  private async resolveNetworkUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    // Try to find in network manager
    const topologies = this.networkManager.getTopologies();
    const topology = topologies.find(top => top.uorId === uorId);
    
    if (topology) {
      return {
        uorId,
        type: 'network_topology',
        found: true,
        data: topology,
        dependencies: this.networkManager.getDependencies().filter(dep => dep.targetUorId === uorId).map(dep => dep.sourceUorId),
        holographicFingerprint: topology.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'network_manager',
          confidence: 1.0
        }
      };
    }

    // Try to find CTP-96 sessions
    const sessions = this.networkManager.getCTP96Sessions();
    const session = sessions.find(sess => sess.uorId === uorId);
    
    if (session) {
      return {
        uorId,
        type: 'ctp96_session',
        found: true,
        data: session,
        dependencies: [session.sourceUorId, session.targetUorId],
        holographicFingerprint: session.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'network_manager',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'network');
  }

  /**
   * Resolve storage UOR
   */
  private async resolveStorageUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    // Try to find in storage manager
    const storageSystems = this.storageManager.getStorageSystems();
    const storageSystem = storageSystems.find(sys => sys.uorId === uorId);
    
    if (storageSystem) {
      return {
        uorId,
        type: 'storage_system',
        found: true,
        data: storageSystem,
        dependencies: this.storageManager.getDependencies().filter(dep => dep.targetUorId === uorId).map(dep => dep.sourceUorId),
        holographicFingerprint: storageSystem.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'storage_manager',
          confidence: 1.0
        }
      };
    }

    // Try to find volumes
    const volumes = this.storageManager.getVolumes();
    const volume = volumes.find(vol => vol.uorId === uorId);
    
    if (volume) {
      return {
        uorId,
        type: 'storage_volume',
        found: true,
        data: volume,
        dependencies: [volume.storageSystemUorId],
        holographicFingerprint: volume.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'storage_manager',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'storage');
  }

  /**
   * Resolve IaC UOR
   */
  private async resolveIaCUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    // Try to find in IaC manager
    const definitions = this.iacManager.getDefinitions();
    const definition = definitions.find(def => def.uorId === uorId);
    
    if (definition) {
      return {
        uorId,
        type: 'infrastructure_definition',
        found: true,
        data: definition,
        dependencies: this.iacManager.getDependencies().filter((dep: any) => dep.targetUorId === uorId).map((dep: any) => dep.sourceUorId),
        holographicFingerprint: definition.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'iac_manager',
          confidence: 1.0
        }
      };
    }

    // Try to find deployments
    const deployments = this.iacManager.getDeployments();
    const deployment = deployments.find(dep => dep.uorId === uorId);
    
    if (deployment) {
      return {
        uorId,
        type: 'infrastructure_deployment',
        found: true,
        data: deployment,
        dependencies: deployment.resources.map(res => res.uorId),
        holographicFingerprint: deployment.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'iac_manager',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'iac');
  }

  /**
   * Resolve component UOR
   */
  private async resolveComponentUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    const components = this.orchestrator.getComponents();
    const component = components.find(comp => comp.uorId === uorId);
    
    if (component) {
      return {
        uorId,
        type: 'infrastructure_component',
        found: true,
        data: component,
        dependencies: component.dependencies,
        holographicFingerprint: component.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'orchestrator',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'component');
  }

  /**
   * Resolve deployment UOR
   */
  private async resolveDeploymentUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    const deployments = this.orchestrator.getDeployments();
    const deployment = deployments.find(dep => dep.uorId === uorId);
    
    if (deployment) {
      return {
        uorId,
        type: 'infrastructure_deployment',
        found: true,
        data: deployment,
        dependencies: deployment.dependencies.map(dep => dep.uorId),
        holographicFingerprint: deployment.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'orchestrator',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'deployment');
  }

  /**
   * Resolve dependency UOR
   */
  private async resolveDependencyUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    // Try to find in orchestrator dependencies
    const dependencies = this.orchestrator.getDependencies();
    const dependency = dependencies.find(dep => dep.uorId === uorId);
    
    if (dependency) {
      return {
        uorId,
        type: 'infrastructure_dependency',
        found: true,
        data: dependency,
        dependencies: [dependency.sourceUorId, dependency.targetUorId],
        holographicFingerprint: dependency.holographicFingerprint,
        metadata: {
          resolvedAt: new Date().toISOString(),
          resolutionTime: 0,
          source: 'orchestrator',
          confidence: 1.0
        }
      };
    }

    return this.createNotFoundResult(uorId, 'dependency');
  }

  /**
   * Resolve generic UOR (fallback)
   */
  private async resolveGenericUOR(uorId: string): Promise<InfrastructureResolutionResult> {
    // Try all managers as fallback
    const allManagers = [
      this.databaseTracker,
      this.iacManager,
      this.networkManager,
      this.storageManager,
      this.orchestrator
    ];

    for (const manager of allManagers) {
      try {
        // This is a simplified approach - in practice, each manager would have a generic resolve method
        const result = await this.tryResolveInManager(manager, uorId);
        if (result.found) {
          return result;
        }
      } catch (error) {
        // Continue to next manager
        continue;
      }
    }

    return this.createNotFoundResult(uorId, 'unknown');
  }

  /**
   * Try to resolve UOR in a specific manager
   */
  private async tryResolveInManager(manager: any, uorId: string): Promise<InfrastructureResolutionResult> {
    // This is a simplified implementation - each manager would implement a resolve method
    return this.createNotFoundResult(uorId, 'unknown');
  }

  /**
   * Create not found result
   */
  private createNotFoundResult(uorId: string, type: string): InfrastructureResolutionResult {
    return {
      uorId,
      type,
      found: false,
      data: null,
      dependencies: [],
      holographicFingerprint: ccmHash(uorId, "not_found"),
      metadata: {
        resolvedAt: new Date().toISOString(),
        resolutionTime: 0,
        source: 'not_found',
        confidence: 0.0
      }
    };
  }

  /**
   * Query infrastructure components
   */
  async queryInfrastructure(query: InfrastructureQuery): Promise<InfrastructureResolutionResult[]> {
    const results: InfrastructureResolutionResult[] = [];

    // Query database components
    if (!query.type || query.type === 'database') {
      const dbResults = await this.queryDatabaseComponents(query);
      results.push(...dbResults);
    }

    // Query network components
    if (!query.type || query.type === 'network') {
      const networkResults = await this.queryNetworkComponents(query);
      results.push(...networkResults);
    }

    // Query storage components
    if (!query.type || query.type === 'storage') {
      const storageResults = await this.queryStorageComponents(query);
      results.push(...storageResults);
    }

    // Query IaC components
    if (!query.type || query.type === 'iac') {
      const iacResults = await this.queryIaCComponents(query);
      results.push(...iacResults);
    }

    // Query orchestrator components
    if (!query.type || query.type === 'component' || query.type === 'deployment') {
      const orchestratorResults = await this.queryOrchestratorComponents(query);
      results.push(...orchestratorResults);
    }

    // Apply filters
    const filteredResults = this.applyQueryFilters(results, query);

    // Apply pagination
    const paginatedResults = this.applyPagination(filteredResults, query);

    this.metrics.inc("infrastructure_queries");
    return paginatedResults;
  }

  /**
   * Query database components
   */
  private async queryDatabaseComponents(query: InfrastructureQuery): Promise<InfrastructureResolutionResult[]> {
    const results: InfrastructureResolutionResult[] = [];
    
    const connections = this.databaseTracker.getConnections();
    for (const connection of connections) {
      if (this.matchesQuery(connection, query)) {
        const result = await this.resolveDatabaseUOR(connection.uorId);
        results.push(result);
      }
    }

    return results;
  }

  /**
   * Query network components
   */
  private async queryNetworkComponents(query: InfrastructureQuery): Promise<InfrastructureResolutionResult[]> {
    const results: InfrastructureResolutionResult[] = [];
    
    const topologies = this.networkManager.getTopologies();
    for (const topology of topologies) {
      if (this.matchesQuery(topology, query)) {
        const result = await this.resolveNetworkUOR(topology.uorId);
        results.push(result);
      }
    }

    return results;
  }

  /**
   * Query storage components
   */
  private async queryStorageComponents(query: InfrastructureQuery): Promise<InfrastructureResolutionResult[]> {
    const results: InfrastructureResolutionResult[] = [];
    
    const storageSystems = this.storageManager.getStorageSystems();
    for (const storageSystem of storageSystems) {
      if (this.matchesQuery(storageSystem, query)) {
        const result = await this.resolveStorageUOR(storageSystem.uorId);
        results.push(result);
      }
    }

    return results;
  }

  /**
   * Query IaC components
   */
  private async queryIaCComponents(query: InfrastructureQuery): Promise<InfrastructureResolutionResult[]> {
    const results: InfrastructureResolutionResult[] = [];
    
    const definitions = this.iacManager.getDefinitions();
    for (const definition of definitions) {
      if (this.matchesQuery(definition, query)) {
        const result = await this.resolveIaCUOR(definition.uorId);
        results.push(result);
      }
    }

    return results;
  }

  /**
   * Query orchestrator components
   */
  private async queryOrchestratorComponents(query: InfrastructureQuery): Promise<InfrastructureResolutionResult[]> {
    const results: InfrastructureResolutionResult[] = [];
    
    const components = this.orchestrator.getComponents();
    for (const component of components) {
      if (this.matchesQuery(component, query)) {
        const result = await this.resolveComponentUOR(component.uorId);
        results.push(result);
      }
    }

    return results;
  }

  /**
   * Check if component matches query
   */
  private matchesQuery(component: any, query: InfrastructureQuery): boolean {
    if (query.name && component.name !== query.name) return false;
    if (query.provider && component.provider !== query.provider) return false;
    if (query.region && component.region !== query.region) return false;
    if (query.environment && component.environment !== query.environment) return false;
    
    if (query.tags && query.tags.length > 0) {
      const componentTags = component.tags || component.metadata?.tags || [];
      if (!query.tags.every(tag => componentTags.includes(tag))) return false;
    }

    if (query.properties) {
      for (const [key, value] of Object.entries(query.properties)) {
        if (component.properties?.[key] !== value) return false;
      }
    }

    return true;
  }

  /**
   * Apply query filters
   */
  private applyQueryFilters(results: InfrastructureResolutionResult[], query: InfrastructureQuery): InfrastructureResolutionResult[] {
    return results.filter(result => {
      if (query.type && result.type !== query.type) return false;
      return true;
    });
  }

  /**
   * Apply pagination
   */
  private applyPagination(results: InfrastructureResolutionResult[], query: InfrastructureQuery): InfrastructureResolutionResult[] {
    const offset = query.offset || 0;
    const limit = query.limit || 100;
    
    return results.slice(offset, offset + limit);
  }

  /**
   * Build dependency graph
   */
  async buildDependencyGraph(rootUorId: string, maxDepth: number = 5): Promise<InfrastructureDependencyGraph> {
    const uorId = this.generateUORId('dependency_graph', rootUorId);
    const nodes: InfrastructureGraphNode[] = [];
    const edges: InfrastructureGraphEdge[] = [];
    const visited = new Set<string>();

    await this.buildDependencyGraphRecursive(rootUorId, nodes, edges, visited, 0, maxDepth);

    const graph: InfrastructureDependencyGraph = {
      uorId,
      rootUorId,
      nodes,
      edges,
      holographicFingerprint: this.generateHolographicFingerprint(uorId, { rootUorId, nodes, edges }),
      metadata: {
        createdAt: new Date().toISOString(),
        lastUpdated: new Date().toISOString(),
        totalNodes: nodes.length,
        totalEdges: edges.length,
        maxDepth: Math.max(...nodes.map(n => n.metadata.createdAt ? 0 : 0)) // Simplified
      }
    };

    this.dependencyGraphs.set(uorId, graph);
    this.metrics.inc("infrastructure_dependency_graphs_built");

    return graph;
  }

  /**
   * Build dependency graph recursively
   */
  private async buildDependencyGraphRecursive(
    uorId: string,
    nodes: InfrastructureGraphNode[],
    edges: InfrastructureGraphEdge[],
    visited: Set<string>,
    depth: number,
    maxDepth: number
  ): Promise<void> {
    if (visited.has(uorId) || depth >= maxDepth) return;
    
    visited.add(uorId);

    try {
      const result = await this.resolveUOR(uorId);
      
      if (result.found) {
        // Add node
        const node: InfrastructureGraphNode = {
          uorId,
          type: result.type,
          name: result.data?.name || uorId,
          properties: result.data?.properties || {},
          metadata: {
            createdAt: result.data?.metadata?.createdAt || new Date().toISOString(),
            lastModified: result.data?.metadata?.lastModified || new Date().toISOString(),
            status: result.data?.status || 'unknown',
            health: result.data?.metadata?.health || 'unknown'
          }
        };
        nodes.push(node);

        // Process dependencies
        for (const depUorId of result.dependencies) {
          // Add edge
          const edge: InfrastructureGraphEdge = {
            sourceUorId: uorId,
            targetUorId: depUorId,
            relationship: 'depends_on',
            weight: 1.0,
            properties: {}
          };
          edges.push(edge);

          // Recursively process dependency
          await this.buildDependencyGraphRecursive(depUorId, nodes, edges, visited, depth + 1, maxDepth);
        }
      }
    } catch (error) {
      // Skip if resolution fails
      console.warn(`Failed to resolve UOR ${uorId} in dependency graph:`, error);
    }
  }

  /**
   * Extract UOR type from ID
   */
  private extractUORType(uorId: string): string {
    const parts = uorId.split('/');
    if (parts.length >= 4) {
      return parts[3]; // atlas-12288/infrastructure/{type}/...
    }
    return 'unknown';
  }

  /**
   * Check if cache is valid
   */
  private isCacheValid(result: InfrastructureResolutionResult): boolean {
    const age = Date.now() - new Date(result.metadata.resolvedAt).getTime();
    return age < this.config.cacheTimeoutMs;
  }

  /**
   * Cache result
   */
  private cacheResult(uorId: string, result: InfrastructureResolutionResult): void {
    // Implement LRU cache eviction if needed
    if (this.cache.size >= this.config.maxCacheSize) {
      const firstKey = this.cache.keys().next().value;
      if (firstKey !== undefined) {
        this.cache.delete(firstKey);
      }
    }
    
    this.cache.set(uorId, result);
  }

  /**
   * Update mapping access
   */
  private updateMappingAccess(uorId: string): void {
    const mapping = this.mappings.get(uorId);
    if (mapping) {
      mapping.metadata.lastAccessed = new Date().toISOString();
      mapping.metadata.accessCount++;
      this.mappings.set(uorId, mapping);
    }
  }

  /**
   * Calculate confidence score
   */
  private calculateConfidence(result: InfrastructureResolutionResult): number {
    if (!result.found) return 0.0;
    
    let confidence = 1.0;
    
    // Reduce confidence based on resolution time
    if (result.metadata.resolutionTime > 1000) {
      confidence *= 0.9;
    }
    
    // Reduce confidence if no dependencies found (might be incomplete)
    if (result.dependencies.length === 0) {
      confidence *= 0.8;
    }
    
    return Math.max(0.0, Math.min(1.0, confidence));
  }

  /**
   * Get all mappings
   */
  getMappings(): InfrastructureUORMapping[] {
    return Array.from(this.mappings.values());
  }

  /**
   * Get cache statistics
   */
  getCacheStats(): { size: number; hitRate: number } {
    return {
      size: this.cache.size,
      hitRate: this.metrics.getCounter("infrastructure_uor_cache_hits") / 
               (this.metrics.getCounter("infrastructure_uor_cache_hits") + this.metrics.getCounter("infrastructure_uor_resolutions"))
    };
  }

  /**
   * Get dependency graphs
   */
  getDependencyGraphs(): InfrastructureDependencyGraph[] {
    return Array.from(this.dependencyGraphs.values());
  }

  /**
   * Generate UOR-ID
   */
  private generateUORId(type: string, ...parts: string[]): string {
    const content = `${type}:${parts.join(':')}`;
    return `atlas-12288/infrastructure/resolver/${ccmHash(content, "uor_id")}`;
  }

  /**
   * Generate holographic fingerprint
   */
  private generateHolographicFingerprint(uorId: string, data: any): string {
    return ccmHash(JSON.stringify({ uorId, data }), "holographic_fingerprint");
  }

  /**
   * Cleanup old data
   */
  async cleanup(): Promise<void> {
    const cutoffDate = new Date(Date.now() - (this.config.retentionDays * 24 * 60 * 60 * 1000));
    
    // Clean up old mappings
    for (const [uorId, mapping] of this.mappings) {
      if (new Date(mapping.metadata.lastAccessed) < cutoffDate) {
        this.mappings.delete(uorId);
        this.metrics.inc("infrastructure_mappings_cleaned");
      }
    }

    // Clean up old cache entries
    for (const [uorId, result] of this.cache) {
      if (new Date(result.metadata.resolvedAt) < cutoffDate) {
        this.cache.delete(uorId);
        this.metrics.inc("infrastructure_cache_entries_cleaned");
      }
    }

    // Clean up old dependency graphs
    for (const [uorId, graph] of this.dependencyGraphs) {
      if (new Date(graph.metadata.createdAt) < cutoffDate) {
        this.dependencyGraphs.delete(uorId);
        this.metrics.inc("infrastructure_dependency_graphs_cleaned");
      }
    }
  }
}

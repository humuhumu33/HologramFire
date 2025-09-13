/**
 * Enhanced Network Manager
 * 
 * Extends the basic networking system with advanced features including CTP-96 implementation,
 * network topology tracking, and cross-modal network dependencies as part of the UOR framework.
 */

import { ccmHash } from "../../crypto/ccm/CCMHash";
import { Metrics } from "../../monitoring/metrics/Metrics";

export interface NetworkTopology {
  uorId: string;
  name: string;
  type: 'vpc' | 'subnet' | 'bridge' | 'overlay' | 'mesh' | 'hybrid';
  nodes: NetworkNode[];
  edges: NetworkEdge[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    version: string;
    region: string;
    provider: string;
    cidrBlocks: string[];
    dnsServers: string[];
  };
}

export interface NetworkNode {
  uorId: string;
  name: string;
  type: 'router' | 'switch' | 'firewall' | 'load_balancer' | 'gateway' | 'endpoint' | 'container' | 'vm';
  properties: {
    ipAddress?: string;
    macAddress?: string;
    port?: number;
    protocol?: string;
    status: 'active' | 'inactive' | 'maintenance' | 'failed';
    capabilities: string[];
    bandwidth?: number;
    latency?: number;
  };
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastSeen: string;
    region: string;
    availabilityZone?: string;
    tags: string[];
  };
}

export interface NetworkEdge {
  uorId: string;
  sourceUorId: string;
  targetUorId: string;
  type: 'physical' | 'logical' | 'tunnel' | 'vpn' | 'overlay';
  properties: {
    bandwidth: number;
    latency: number;
    jitter: number;
    packetLoss: number;
    mtu: number;
    encryption: boolean;
    protocol: string;
  };
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    status: 'up' | 'down' | 'degraded';
    utilization: number;
    errorRate: number;
  };
}

export interface CTP96Session {
  uorId: string;
  name: string;
  type: 'unicast' | 'multicast' | 'broadcast' | 'anycast';
  sourceUorId: string;
  targetUorId: string;
  protocol: 'tcp' | 'udp' | 'icmp' | 'http' | 'https' | 'grpc' | 'websocket';
  properties: {
    port: number;
    encryption: boolean;
    compression: boolean;
    qualityOfService: 'best_effort' | 'controlled_load' | 'guaranteed';
    priority: number;
    timeout: number;
    retryCount: number;
  };
  holographicFingerprint: string;
  witnessSignature: string;
  metadata: {
    createdAt: string;
    lastActivity: string;
    status: 'active' | 'idle' | 'closed' | 'error';
    bytesTransferred: number;
    packetsTransferred: number;
    connectionTime: number;
  };
}

export interface NetworkSecurityPolicy {
  uorId: string;
  name: string;
  type: 'firewall' | 'acl' | 'security_group' | 'waf' | 'ids' | 'ips';
  rules: SecurityRule[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    author: string;
    environment: string;
    priority: number;
  };
}

export interface SecurityRule {
  uorId: string;
  name: string;
  action: 'allow' | 'deny' | 'log' | 'redirect';
  source: NetworkAddress;
  destination: NetworkAddress;
  protocol: string;
  port?: number;
  direction: 'ingress' | 'egress' | 'both';
  conditions: SecurityCondition[];
  holographicFingerprint: string;
  metadata: {
    createdAt: string;
    lastModified: string;
    priority: number;
    enabled: boolean;
  };
}

export interface NetworkAddress {
  type: 'ip' | 'cidr' | 'hostname' | 'tag' | 'security_group';
  value: string;
  port?: number;
}

export interface SecurityCondition {
  field: string;
  operator: 'equals' | 'not_equals' | 'contains' | 'not_contains' | 'in' | 'not_in' | 'matches' | 'not_matches';
  value: any;
}

export interface NetworkDependency {
  uorId: string;
  sourceUorId: string; // Source service or application
  targetUorId: string; // Target service or network resource
  dependencyType: 'depends_on' | 'communicates_with' | 'routes_through' | 'load_balances' | 'proxies';
  networkPath: NetworkPath[];
  holographicFingerprint: string;
  witnessSignature: string;
  metadata: {
    createdAt: string;
    lastUsed: string;
    frequency: number;
    criticality: 'low' | 'medium' | 'high' | 'critical';
    latency: number;
    bandwidth: number;
  };
}

export interface NetworkPath {
  hop: number;
  nodeUorId: string;
  edgeUorId?: string;
  latency: number;
  bandwidth: number;
  properties: Record<string, any>;
}

export interface NetworkPerformanceMetrics {
  uorId: string;
  networkUorId: string;
  timestamp: string;
  metrics: {
    throughput: {
      bytesPerSecond: number;
      packetsPerSecond: number;
      bitsPerSecond: number;
    };
    latency: {
      average: number;
      min: number;
      max: number;
      p95: number;
      p99: number;
    };
    reliability: {
      packetLoss: number;
      errorRate: number;
      uptime: number;
    };
    utilization: {
      bandwidth: number;
      connections: number;
      cpu: number;
      memory: number;
    };
  };
  holographicFingerprint: string;
}

export interface EnhancedNetworkManagerConfig {
  enableCTP96: boolean;
  enableTopologyDiscovery: boolean;
  enableSecurityPolicies: boolean;
  enablePerformanceMonitoring: boolean;
  enableDependencyTracking: boolean;
  discoveryIntervalMs: number;
  monitoringIntervalMs: number;
  retentionDays: number;
  maxSessionsPerNode: number;
}

export class EnhancedNetworkManager {
  private config: EnhancedNetworkManagerConfig;
  private metrics: Metrics;
  private topologies: Map<string, NetworkTopology> = new Map();
  private nodes: Map<string, NetworkNode> = new Map();
  private edges: Map<string, NetworkEdge> = new Map();
  private ctp96Sessions: Map<string, CTP96Session> = new Map();
  private securityPolicies: Map<string, NetworkSecurityPolicy> = new Map();
  private dependencies: Map<string, NetworkDependency> = new Map();
  private performanceMetrics: Map<string, NetworkPerformanceMetrics[]> = new Map();
  private discoveryTimer: NodeJS.Timeout | null = null;
  private monitoringTimer: NodeJS.Timeout | null = null;

  constructor(config: Partial<EnhancedNetworkManagerConfig> = {}, metrics: Metrics) {
    this.config = {
      enableCTP96: config.enableCTP96 !== false,
      enableTopologyDiscovery: config.enableTopologyDiscovery !== false,
      enableSecurityPolicies: config.enableSecurityPolicies !== false,
      enablePerformanceMonitoring: config.enablePerformanceMonitoring !== false,
      enableDependencyTracking: config.enableDependencyTracking !== false,
      discoveryIntervalMs: config.discoveryIntervalMs || 30000,
      monitoringIntervalMs: config.monitoringIntervalMs || 10000,
      retentionDays: config.retentionDays || 30,
      maxSessionsPerNode: config.maxSessionsPerNode || 1000,
      ...config
    };
    this.metrics = metrics;
  }

  /**
   * Create network topology
   */
  async createTopology(
    name: string,
    type: NetworkTopology['type'],
    metadata: Partial<NetworkTopology['metadata']> = {}
  ): Promise<NetworkTopology> {
    const uorId = this.generateUORId('topology', name, type);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, type });

    const topology: NetworkTopology = {
      uorId,
      name,
      type,
      nodes: [],
      edges: [],
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        version: '1.0.0',
        region: 'us-east-1',
        provider: 'aws',
        cidrBlocks: [],
        dnsServers: [],
        ...metadata
      }
    };

    this.topologies.set(uorId, topology);
    this.metrics.inc("network_topologies_created");

    return topology;
  }

  /**
   * Add network node
   */
  async addNode(
    topologyUorId: string,
    name: string,
    type: NetworkNode['type'],
    properties: Partial<NetworkNode['properties']> = {},
    metadata: Partial<NetworkNode['metadata']> = {}
  ): Promise<NetworkNode> {
    const topology = this.topologies.get(topologyUorId);
    if (!topology) {
      throw new Error(`Topology ${topologyUorId} not found`);
    }

    const uorId = this.generateUORId('node', topologyUorId, name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, type, properties });

    const node: NetworkNode = {
      uorId,
      name,
      type,
      properties: {
        status: 'active',
        capabilities: [],
        ...properties
      },
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastSeen: new Date().toISOString(),
        region: 'us-east-1',
        tags: [],
        ...metadata
      }
    };

    this.nodes.set(uorId, node);
    topology.nodes.push(node);
    topology.metadata.lastModified = new Date().toISOString();
    this.topologies.set(topologyUorId, topology);

    this.metrics.inc("network_nodes_added");
    return node;
  }

  /**
   * Add network edge
   */
  async addEdge(
    topologyUorId: string,
    sourceUorId: string,
    targetUorId: string,
    type: NetworkEdge['type'],
    properties: Partial<NetworkEdge['properties']> = {},
    metadata: Partial<NetworkEdge['metadata']> = {}
  ): Promise<NetworkEdge> {
    const topology = this.topologies.get(topologyUorId);
    if (!topology) {
      throw new Error(`Topology ${topologyUorId} not found`);
    }

    const uorId = this.generateUORId('edge', topologyUorId, sourceUorId, targetUorId);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { sourceUorId, targetUorId, type });

    const edge: NetworkEdge = {
      uorId,
      sourceUorId,
      targetUorId,
      type,
      properties: {
        bandwidth: 1000000000, // 1 Gbps
        latency: 1,
        jitter: 0.1,
        packetLoss: 0,
        mtu: 1500,
        encryption: false,
        protocol: 'ethernet',
        ...properties
      },
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        status: 'up',
        utilization: 0,
        errorRate: 0,
        ...metadata
      }
    };

    this.edges.set(uorId, edge);
    topology.edges.push(edge);
    topology.metadata.lastModified = new Date().toISOString();
    this.topologies.set(topologyUorId, topology);

    this.metrics.inc("network_edges_added");
    return edge;
  }

  /**
   * Create CTP-96 session
   */
  async createCTP96Session(
    name: string,
    sourceUorId: string,
    targetUorId: string,
    protocol: CTP96Session['protocol'],
    properties: Partial<CTP96Session['properties']> = {}
  ): Promise<CTP96Session> {
    if (!this.config.enableCTP96) {
      throw new Error("CTP-96 is not enabled");
    }

    const uorId = this.generateUORId('ctp96_session', name, sourceUorId, targetUorId);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, sourceUorId, targetUorId });
    const witnessSignature = await this.generateWitnessSignature(uorId, { name, sourceUorId, targetUorId });

    const session: CTP96Session = {
      uorId,
      name,
      type: 'unicast',
      sourceUorId,
      targetUorId,
      protocol,
      properties: {
        port: 80,
        encryption: false,
        compression: false,
        qualityOfService: 'best_effort',
        priority: 0,
        timeout: 30000,
        retryCount: 3,
        ...properties
      },
      holographicFingerprint,
      witnessSignature,
      metadata: {
        createdAt: new Date().toISOString(),
        lastActivity: new Date().toISOString(),
        status: 'active',
        bytesTransferred: 0,
        packetsTransferred: 0,
        connectionTime: 0
      }
    };

    this.ctp96Sessions.set(uorId, session);
    this.metrics.inc("ctp96_sessions_created");

    return session;
  }

  /**
   * Create security policy
   */
  async createSecurityPolicy(
    name: string,
    type: NetworkSecurityPolicy['type'],
    rules: SecurityRule[],
    metadata: Partial<NetworkSecurityPolicy['metadata']> = {}
  ): Promise<NetworkSecurityPolicy> {
    const uorId = this.generateUORId('security_policy', name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, type, rules });

    const policy: NetworkSecurityPolicy = {
      uorId,
      name,
      type,
      rules,
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        author: 'system',
        environment: 'production',
        priority: 100,
        ...metadata
      }
    };

    this.securityPolicies.set(uorId, policy);
    this.metrics.inc("security_policies_created");

    return policy;
  }

  /**
   * Create security rule
   */
  async createSecurityRule(
    name: string,
    action: SecurityRule['action'],
    source: NetworkAddress,
    destination: NetworkAddress,
    protocol: string,
    conditions: SecurityCondition[] = [],
    metadata: Partial<SecurityRule['metadata']> = {}
  ): Promise<SecurityRule> {
    const uorId = this.generateUORId('security_rule', name);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { name, action, source, destination });

    const rule: SecurityRule = {
      uorId,
      name,
      action,
      source,
      destination,
      protocol,
      direction: 'both',
      conditions,
      holographicFingerprint,
      metadata: {
        createdAt: new Date().toISOString(),
        lastModified: new Date().toISOString(),
        priority: 100,
        enabled: true,
        ...metadata
      }
    };

    return rule;
  }

  /**
   * Track network dependency
   */
  async trackDependency(
    sourceUorId: string,
    targetUorId: string,
    dependencyType: NetworkDependency['dependencyType'],
    networkPath: NetworkPath[] = [],
    metadata: Partial<NetworkDependency['metadata']> = {}
  ): Promise<NetworkDependency> {
    const uorId = this.generateUORId('network_dependency', sourceUorId, targetUorId);
    const holographicFingerprint = this.generateHolographicFingerprint(uorId, { sourceUorId, targetUorId, dependencyType });
    const witnessSignature = await this.generateWitnessSignature(uorId, { sourceUorId, targetUorId, dependencyType });

    const dependency: NetworkDependency = {
      uorId,
      sourceUorId,
      targetUorId,
      dependencyType,
      networkPath,
      holographicFingerprint,
      witnessSignature,
      metadata: {
        createdAt: new Date().toISOString(),
        lastUsed: new Date().toISOString(),
        frequency: 1,
        criticality: 'medium',
        latency: this.calculatePathLatency(networkPath),
        bandwidth: this.calculatePathBandwidth(networkPath),
        ...metadata
      }
    };

    this.dependencies.set(uorId, dependency);
    this.metrics.inc("network_dependencies_tracked");

    return dependency;
  }

  /**
   * Discover network topology
   */
  async discoverTopology(topologyUorId: string): Promise<void> {
    const topology = this.topologies.get(topologyUorId);
    if (!topology) {
      throw new Error(`Topology ${topologyUorId} not found`);
    }

    try {
      // Mock topology discovery - would integrate with actual network discovery tools
      const discoveredNodes = await this.performNetworkDiscovery(topology);
      const discoveredEdges = await this.performEdgeDiscovery(topology, discoveredNodes);

      // Update topology with discovered nodes and edges
      topology.nodes = discoveredNodes;
      topology.edges = discoveredEdges;
      topology.metadata.lastModified = new Date().toISOString();

      this.topologies.set(topologyUorId, topology);
      this.metrics.inc("network_topologies_discovered");
    } catch (error) {
      this.metrics.inc("network_topology_discovery_errors");
      console.error(`Topology discovery failed for ${topology.name}:`, error);
    }
  }

  /**
   * Perform network discovery (mock implementation)
   */
  private async performNetworkDiscovery(topology: NetworkTopology): Promise<NetworkNode[]> {
    // Mock discovery - would use actual network discovery protocols
    const mockNodes: NetworkNode[] = [
      {
        uorId: this.generateUORId('node', topology.uorId, 'router-1'),
        name: 'router-1',
        type: 'router',
        properties: {
          ipAddress: '10.0.1.1',
          status: 'active',
          capabilities: ['routing', 'nat', 'firewall'],
          bandwidth: 10000000000, // 10 Gbps
          latency: 0.1
        },
        holographicFingerprint: this.generateHolographicFingerprint('router-1', { topology: topology.uorId }),
        metadata: {
          createdAt: new Date().toISOString(),
          lastSeen: new Date().toISOString(),
          region: 'us-east-1',
          availabilityZone: 'us-east-1a',
          tags: ['core', 'routing']
        }
      },
      {
        uorId: this.generateUORId('node', topology.uorId, 'switch-1'),
        name: 'switch-1',
        type: 'switch',
        properties: {
          ipAddress: '10.0.1.2',
          status: 'active',
          capabilities: ['switching', 'vlans'],
          bandwidth: 1000000000, // 1 Gbps
          latency: 0.01
        },
        holographicFingerprint: this.generateHolographicFingerprint('switch-1', { topology: topology.uorId }),
        metadata: {
          createdAt: new Date().toISOString(),
          lastSeen: new Date().toISOString(),
          region: 'us-east-1',
          availabilityZone: 'us-east-1a',
          tags: ['switching', 'access']
        }
      }
    ];

    return mockNodes;
  }

  /**
   * Perform edge discovery (mock implementation)
   */
  private async performEdgeDiscovery(topology: NetworkTopology, nodes: NetworkNode[]): Promise<NetworkEdge[]> {
    // Mock edge discovery
    if (nodes.length < 2) return [];

    const edges: NetworkEdge[] = [];
    
    for (let i = 0; i < nodes.length - 1; i++) {
      const source = nodes[i];
      const target = nodes[i + 1];
      
      const edge: NetworkEdge = {
        uorId: this.generateUORId('edge', topology.uorId, source.uorId, target.uorId),
        sourceUorId: source.uorId,
        targetUorId: target.uorId,
        type: 'physical',
        properties: {
          bandwidth: Math.min(source.properties.bandwidth || 1000000000, target.properties.bandwidth || 1000000000),
          latency: (source.properties.latency || 0) + (target.properties.latency || 0) + 0.1,
          jitter: 0.1,
          packetLoss: 0,
          mtu: 1500,
          encryption: false,
          protocol: 'ethernet'
        },
        holographicFingerprint: this.generateHolographicFingerprint('edge', { source: source.uorId, target: target.uorId }),
        metadata: {
          createdAt: new Date().toISOString(),
          lastModified: new Date().toISOString(),
          status: 'up',
          utilization: 0,
          errorRate: 0
        }
      };

      edges.push(edge);
    }

    return edges;
  }

  /**
   * Collect performance metrics
   */
  async collectPerformanceMetrics(networkUorId: string): Promise<NetworkPerformanceMetrics> {
    const topology = this.topologies.get(networkUorId);
    if (!topology) {
      throw new Error(`Topology ${networkUorId} not found`);
    }

    const uorId = this.generateUORId('performance_metrics', networkUorId, Date.now().toString());
    
    // Mock performance metrics collection
    const metrics: NetworkPerformanceMetrics = {
      uorId,
      networkUorId,
      timestamp: new Date().toISOString(),
      metrics: {
        throughput: {
          bytesPerSecond: Math.random() * 1000000000, // Random up to 1 GB/s
          packetsPerSecond: Math.random() * 1000000, // Random up to 1M packets/s
          bitsPerSecond: Math.random() * 8000000000 // Random up to 8 Gbps
        },
        latency: {
          average: Math.random() * 10 + 1, // 1-11 ms
          min: Math.random() * 5 + 0.5, // 0.5-5.5 ms
          max: Math.random() * 20 + 5, // 5-25 ms
          p95: Math.random() * 15 + 3, // 3-18 ms
          p99: Math.random() * 25 + 5 // 5-30 ms
        },
        reliability: {
          packetLoss: Math.random() * 0.1, // 0-0.1%
          errorRate: Math.random() * 0.01, // 0-0.01%
          uptime: 99.9 + Math.random() * 0.1 // 99.9-100%
        },
        utilization: {
          bandwidth: Math.random() * 100, // 0-100%
          connections: Math.floor(Math.random() * 10000), // 0-10K connections
          cpu: Math.random() * 100, // 0-100%
          memory: Math.random() * 100 // 0-100%
        }
      },
      holographicFingerprint: this.generateHolographicFingerprint(uorId, { networkUorId, timestamp: Date.now() })
    };

    // Store metrics
    if (!this.performanceMetrics.has(networkUorId)) {
      this.performanceMetrics.set(networkUorId, []);
    }
    
    const metricsList = this.performanceMetrics.get(networkUorId)!;
    metricsList.push(metrics);
    
    // Keep only recent metrics
    const cutoffTime = Date.now() - (this.config.retentionDays * 24 * 60 * 60 * 1000);
    const filteredMetrics = metricsList.filter(m => new Date(m.timestamp).getTime() > cutoffTime);
    this.performanceMetrics.set(networkUorId, filteredMetrics);

    this.metrics.inc("network_performance_metrics_collected");
    return metrics;
  }

  /**
   * Start monitoring
   */
  startMonitoring(): void {
    if (this.config.enableTopologyDiscovery && !this.discoveryTimer) {
      this.discoveryTimer = setInterval(async () => {
        await this.performPeriodicDiscovery();
      }, this.config.discoveryIntervalMs);
    }

    if (this.config.enablePerformanceMonitoring && !this.monitoringTimer) {
      this.monitoringTimer = setInterval(async () => {
        await this.performPeriodicMonitoring();
      }, this.config.monitoringIntervalMs);
    }
  }

  /**
   * Stop monitoring
   */
  stopMonitoring(): void {
    if (this.discoveryTimer) {
      clearInterval(this.discoveryTimer);
      this.discoveryTimer = null;
    }

    if (this.monitoringTimer) {
      clearInterval(this.monitoringTimer);
      this.monitoringTimer = null;
    }
  }

  /**
   * Perform periodic discovery
   */
  private async performPeriodicDiscovery(): Promise<void> {
    for (const [uorId, topology] of this.topologies) {
      try {
        await this.discoverTopology(uorId);
      } catch (error) {
        this.metrics.inc("periodic_discovery_errors");
        console.error(`Periodic discovery failed for topology ${topology.name}:`, error);
      }
    }
  }

  /**
   * Perform periodic monitoring
   */
  private async performPeriodicMonitoring(): Promise<void> {
    for (const [uorId, topology] of this.topologies) {
      try {
        await this.collectPerformanceMetrics(uorId);
      } catch (error) {
        this.metrics.inc("periodic_monitoring_errors");
        console.error(`Periodic monitoring failed for topology ${topology.name}:`, error);
      }
    }
  }

  /**
   * Get all topologies
   */
  getTopologies(): NetworkTopology[] {
    return Array.from(this.topologies.values());
  }

  /**
   * Get all CTP-96 sessions
   */
  getCTP96Sessions(): CTP96Session[] {
    return Array.from(this.ctp96Sessions.values());
  }

  /**
   * Get all security policies
   */
  getSecurityPolicies(): NetworkSecurityPolicy[] {
    return Array.from(this.securityPolicies.values());
  }

  /**
   * Get all network dependencies
   */
  getDependencies(): NetworkDependency[] {
    return Array.from(this.dependencies.values());
  }

  /**
   * Get performance metrics for a network
   */
  getPerformanceMetrics(networkUorId: string): NetworkPerformanceMetrics[] {
    return this.performanceMetrics.get(networkUorId) || [];
  }

  /**
   * Calculate path latency
   */
  private calculatePathLatency(path: NetworkPath[]): number {
    return path.reduce((total, hop) => total + hop.latency, 0);
  }

  /**
   * Calculate path bandwidth
   */
  private calculatePathBandwidth(path: NetworkPath[]): number {
    if (path.length === 0) return 0;
    return Math.min(...path.map(hop => hop.bandwidth));
  }

  /**
   * Generate UOR-ID
   */
  private generateUORId(type: string, ...parts: string[]): string {
    const content = `${type}:${parts.join(':')}`;
    return `atlas-12288/infrastructure/network/${ccmHash(content, "uor_id")}`;
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
    
    // Clean up old CTP-96 sessions
    for (const [uorId, session] of this.ctp96Sessions) {
      if (new Date(session.metadata.createdAt) < cutoffDate) {
        this.ctp96Sessions.delete(uorId);
        this.metrics.inc("ctp96_sessions_cleaned");
      }
    }

    // Clean up old performance metrics
    for (const [networkUorId, metricsList] of this.performanceMetrics) {
      const filteredMetrics = metricsList.filter(m => new Date(m.timestamp) > cutoffDate);
      this.performanceMetrics.set(networkUorId, filteredMetrics);
    }
  }
}

/**
 * Enhanced IPFS Client for Production-Grade Distributed Storage
 * 
 * Implements production-ready IPFS integration with advanced features:
 * - Multi-gateway support with failover
 * - Advanced replication and redundancy
 * - Performance optimization for large-scale deployments
 * - Enhanced content discovery and routing
 * - Production-grade monitoring and metrics
 */

import { create, IPFSHTTPClient } from 'ipfs-http-client';
import { CID } from 'ipfs-http-client';
import { EventEmitter } from 'events';
import { Content, Atlas12288Metadata } from '../graphql/types';
import { Atlas12288Encoder } from '../atlas12288/Atlas12288Encoder';
import { ConservationVerifier } from '../conservation/ConservationVerifier';

export interface EnhancedIPFSConfig {
  gateways: Array<{
    host: string;
    port: number;
    protocol: string;
    priority: number;
    timeout: number;
    retries: number;
  }>;
  replication: {
    minReplicationFactor: number;
    targetReplicationFactor: number;
    maxReplicationFactor: number;
    replicationStrategy: 'geographic' | 'performance' | 'hybrid';
  };
  performance: {
    maxConcurrentRequests: number;
    requestTimeout: number;
    retryAttempts: number;
    circuitBreakerThreshold: number;
    cacheSize: number;
    cacheTTL: number;
  };
  monitoring: {
    metricsEnabled: boolean;
    healthCheckInterval: number;
    performanceTracking: boolean;
  };
}

export interface IPFSGateway {
  id: string;
  host: string;
  port: number;
  protocol: string;
  priority: number;
  timeout: number;
  retries: number;
  status: 'healthy' | 'degraded' | 'unhealthy';
  lastHealthCheck: Date;
  responseTime: number;
  errorRate: number;
  successRate: number;
}

export interface IPFSMetrics {
  totalRequests: number;
  successfulRequests: number;
  failedRequests: number;
  averageResponseTime: number;
  totalBytesTransferred: number;
  cacheHitRate: number;
  replicationFactor: number;
  gatewayFailovers: number;
  circuitBreakerTrips: number;
}

export interface ReplicationInfo {
  cid: string;
  currentReplicationFactor: number;
  targetReplicationFactor: number;
  replicationNodes: string[];
  lastReplicationCheck: Date;
  replicationHealth: 'healthy' | 'degraded' | 'critical';
}

export class EnhancedIPFSClient extends EventEmitter {
  private gateways: Map<string, IPFSGateway>;
  private clients: Map<string, IPFSHTTPClient>;
  private atlasEncoder: Atlas12288Encoder;
  private conservationVerifier: ConservationVerifier;
  private config: EnhancedIPFSConfig;
  private metrics: IPFSMetrics;
  private contentCache: Map<string, any>;
  private replicationTracker: Map<string, ReplicationInfo>;
  private circuitBreakers: Map<string, { failures: number; lastFailure: Date; state: 'closed' | 'open' | 'half-open' }>;
  private healthCheckInterval: NodeJS.Timeout;

  constructor(config: EnhancedIPFSConfig) {
    super();
    
    this.config = config;
    this.gateways = new Map();
    this.clients = new Map();
    this.contentCache = new Map();
    this.replicationTracker = new Map();
    this.circuitBreakers = new Map();
    
    this.atlasEncoder = new Atlas12288Encoder();
    this.conservationVerifier = new ConservationVerifier();
    
    this.metrics = {
      totalRequests: 0,
      successfulRequests: 0,
      failedRequests: 0,
      averageResponseTime: 0,
      totalBytesTransferred: 0,
      cacheHitRate: 0,
      replicationFactor: 0,
      gatewayFailovers: 0,
      circuitBreakerTrips: 0
    };

    this.initializeGateways();
    this.startHealthMonitoring();
  }

  /**
   * Initialize IPFS gateways with priority-based ordering
   */
  private initializeGateways(): void {
    for (const gatewayConfig of this.config.gateways) {
      const gateway: IPFSGateway = {
        id: `${gatewayConfig.host}:${gatewayConfig.port}`,
        host: gatewayConfig.host,
        port: gatewayConfig.port,
        protocol: gatewayConfig.protocol,
        priority: gatewayConfig.priority,
        timeout: gatewayConfig.timeout,
        retries: gatewayConfig.retries,
        status: 'healthy',
        lastHealthCheck: new Date(),
        responseTime: 0,
        errorRate: 0,
        successRate: 1.0
      };

      this.gateways.set(gateway.id, gateway);
      this.initializeGatewayClient(gateway);
    }
  }

  /**
   * Initialize IPFS client for a specific gateway
   */
  private initializeGatewayClient(gateway: IPFSGateway): void {
    try {
      const client = create({
        host: gateway.host,
        port: gateway.port,
        protocol: gateway.protocol,
        timeout: gateway.timeout
      });

      this.clients.set(gateway.id, client);
      this.circuitBreakers.set(gateway.id, {
        failures: 0,
        lastFailure: new Date(),
        state: 'closed'
      });

      console.log(`✅ IPFS Gateway initialized: ${gateway.id}`);
    } catch (error) {
      console.error(`❌ Failed to initialize IPFS Gateway ${gateway.id}:`, error);
      gateway.status = 'unhealthy';
    }
  }

  /**
   * Get the best available gateway based on priority and health
   */
  private getBestGateway(): IPFSGateway | null {
    const healthyGateways = Array.from(this.gateways.values())
      .filter(gateway => gateway.status === 'healthy')
      .sort((a, b) => a.priority - b.priority);

    if (healthyGateways.length === 0) {
      // Fallback to degraded gateways
      const degradedGateways = Array.from(this.gateways.values())
        .filter(gateway => gateway.status === 'degraded')
        .sort((a, b) => a.priority - b.priority);
      
      return degradedGateways[0] || null;
    }

    return healthyGateways[0];
  }

  /**
   * Store content with enhanced replication and monitoring
   */
  async storeContent(content: Content): Promise<string> {
    const startTime = Date.now();
    this.metrics.totalRequests++;

    try {
      // Verify conservation laws before storage
      const conservationValid = await this.conservationVerifier.verifyContent(content);
      if (!conservationValid) {
        throw new Error('Content fails conservation verification');
      }

      // Encode content to atlas-12288 format
      const atlasMetadata = await this.atlasEncoder.encodeContent({
        name: content.name,
        data: content.data,
        mimeType: content.metadata.mimeType || 'application/octet-stream'
      });

      // Create enhanced IPFS content object
      const ipfsContent = {
        content,
        atlasMetadata,
        witness: content.witness,
        metadata: content.metadata,
        replication: {
          targetFactor: this.config.replication.targetReplicationFactor,
          strategy: this.config.replication.replicationStrategy,
          timestamp: new Date().toISOString()
        }
      };

      // Store content with replication
      const cid = await this.storeWithReplication(ipfsContent);
      
      // Track replication
      await this.trackReplication(cid);
      
      // Update metrics
      const responseTime = Date.now() - startTime;
      this.updateMetrics(true, responseTime, JSON.stringify(ipfsContent).length);
      
      this.emit('contentStored', { cid, content, responseTime });
      
      console.log(`✅ Content stored with enhanced replication: ${cid}`);
      return cid;
    } catch (error) {
      this.updateMetrics(false, Date.now() - startTime, 0);
      this.emit('contentStoreFailed', { content, error });
      throw error;
    }
  }

  /**
   * Store content with automatic replication across multiple gateways
   */
  private async storeWithReplication(ipfsContent: any): Promise<string> {
    const primaryGateway = this.getBestGateway();
    if (!primaryGateway) {
      throw new Error('No healthy IPFS gateways available');
    }

    const client = this.clients.get(primaryGateway.id);
    if (!client) {
      throw new Error(`No client available for gateway: ${primaryGateway.id}`);
    }

    // Store on primary gateway
    const result = await client.add(JSON.stringify(ipfsContent), {
      pin: true,
      cidVersion: 1
    });

    const cid = result.cid.toString();

    // Replicate to additional gateways
    await this.replicateContent(cid, ipfsContent);

    return cid;
  }

  /**
   * Replicate content across multiple gateways
   */
  private async replicateContent(cid: string, content: any): Promise<void> {
    const replicationPromises: Promise<void>[] = [];
    const availableGateways = Array.from(this.gateways.values())
      .filter(gateway => gateway.status === 'healthy')
      .sort((a, b) => a.priority - b.priority)
      .slice(1, this.config.replication.targetReplicationFactor);

    for (const gateway of availableGateways) {
      const client = this.clients.get(gateway.id);
      if (client) {
        replicationPromises.push(
          this.replicateToGateway(client, cid, content, gateway.id)
        );
      }
    }

    try {
      await Promise.allSettled(replicationPromises);
    } catch (error) {
      console.warn('Some replications failed:', error);
    }
  }

  /**
   * Replicate content to a specific gateway
   */
  private async replicateToGateway(client: IPFSHTTPClient, cid: string, content: any, gatewayId: string): Promise<void> {
    try {
      await client.add(JSON.stringify(content), {
        pin: true,
        cidVersion: 1
      });
      
      console.log(`✅ Content replicated to gateway: ${gatewayId}`);
    } catch (error) {
      console.error(`❌ Failed to replicate to gateway ${gatewayId}:`, error);
      throw error;
    }
  }

  /**
   * Retrieve content with intelligent caching and failover
   */
  async getContent(cid: string): Promise<Content | null> {
    const startTime = Date.now();
    this.metrics.totalRequests++;

    try {
      // Check cache first
      const cached = this.contentCache.get(cid);
      if (cached && this.isCacheValid(cached)) {
        this.metrics.cacheHitRate = (this.metrics.cacheHitRate + 1) / 2;
        return cached.content;
      }

      // Try multiple gateways with failover
      const content = await this.getContentWithFailover(cid);
      
      if (content) {
        // Cache the result
        this.contentCache.set(cid, {
          content,
          timestamp: Date.now(),
          ttl: this.config.performance.cacheTTL
        });

        // Verify conservation laws
        const conservationValid = await this.conservationVerifier.verifyContent(content);
        if (!conservationValid) {
          throw new Error('Retrieved content fails conservation verification');
        }

        const responseTime = Date.now() - startTime;
        this.updateMetrics(true, responseTime, JSON.stringify(content).length);
        
        this.emit('contentRetrieved', { cid, content, responseTime });
        return content;
      }

      return null;
    } catch (error) {
      this.updateMetrics(false, Date.now() - startTime, 0);
      this.emit('contentRetrievalFailed', { cid, error });
      throw error;
    }
  }

  /**
   * Retrieve content with automatic failover between gateways
   */
  private async getContentWithFailover(cid: string): Promise<Content | null> {
    const gateways = Array.from(this.gateways.values())
      .filter(gateway => gateway.status === 'healthy')
      .sort((a, b) => a.priority - b.priority);

    for (const gateway of gateways) {
      const client = this.clients.get(gateway.id);
      if (!client) continue;

      try {
        const result = await client.cat(cid);
        const contentData = JSON.parse(result.toString());
        
        // Update gateway health
        this.updateGatewayHealth(gateway.id, true, Date.now());
        
        return contentData.content;
      } catch (error) {
        this.updateGatewayHealth(gateway.id, false, Date.now());
        console.warn(`Failed to retrieve from gateway ${gateway.id}:`, error);
        continue;
      }
    }

    throw new Error('All gateways failed to retrieve content');
  }

  /**
   * Track replication health for content
   */
  private async trackReplication(cid: string): Promise<void> {
    const replicationInfo: ReplicationInfo = {
      cid,
      currentReplicationFactor: 1,
      targetReplicationFactor: this.config.replication.targetReplicationFactor,
      replicationNodes: [],
      lastReplicationCheck: new Date(),
      replicationHealth: 'healthy'
    };

    // Check replication across all gateways
    for (const gateway of this.gateways.values()) {
      if (gateway.status === 'healthy') {
        const client = this.clients.get(gateway.id);
        if (client) {
          try {
            await client.cat(cid);
            replicationInfo.replicationNodes.push(gateway.id);
            replicationInfo.currentReplicationFactor++;
          } catch (error) {
            // Content not available on this gateway
          }
        }
      }
    }

    // Determine replication health
    if (replicationInfo.currentReplicationFactor >= this.config.replication.targetReplicationFactor) {
      replicationInfo.replicationHealth = 'healthy';
    } else if (replicationInfo.currentReplicationFactor >= this.config.replication.minReplicationFactor) {
      replicationInfo.replicationHealth = 'degraded';
    } else {
      replicationInfo.replicationHealth = 'critical';
    }

    this.replicationTracker.set(cid, replicationInfo);
    this.metrics.replicationFactor = replicationInfo.currentReplicationFactor;

    this.emit('replicationTracked', replicationInfo);
  }

  /**
   * Start health monitoring for all gateways
   */
  private startHealthMonitoring(): void {
    this.healthCheckInterval = setInterval(async () => {
      await this.performHealthChecks();
    }, this.config.monitoring.healthCheckInterval);
  }

  /**
   * Perform health checks on all gateways
   */
  private async performHealthChecks(): Promise<void> {
    const healthCheckPromises = Array.from(this.gateways.values()).map(
      gateway => this.checkGatewayHealth(gateway)
    );

    await Promise.allSettled(healthCheckPromises);
  }

  /**
   * Check health of a specific gateway
   */
  private async checkGatewayHealth(gateway: IPFSGateway): Promise<void> {
    const client = this.clients.get(gateway.id);
    if (!client) return;

    try {
      const startTime = Date.now();
      await client.version();
      const responseTime = Date.now() - startTime;

      gateway.status = 'healthy';
      gateway.lastHealthCheck = new Date();
      gateway.responseTime = responseTime;
      gateway.successRate = Math.min(1.0, gateway.successRate + 0.1);
      gateway.errorRate = Math.max(0, gateway.errorRate - 0.1);

      // Reset circuit breaker
      const circuitBreaker = this.circuitBreakers.get(gateway.id);
      if (circuitBreaker) {
        circuitBreaker.failures = 0;
        circuitBreaker.state = 'closed';
      }
    } catch (error) {
      gateway.status = 'unhealthy';
      gateway.lastHealthCheck = new Date();
      gateway.errorRate = Math.min(1.0, gateway.errorRate + 0.1);
      gateway.successRate = Math.max(0, gateway.successRate - 0.1);

      // Update circuit breaker
      const circuitBreaker = this.circuitBreakers.get(gateway.id);
      if (circuitBreaker) {
        circuitBreaker.failures++;
        circuitBreaker.lastFailure = new Date();
        
        if (circuitBreaker.failures >= this.config.performance.circuitBreakerThreshold) {
          circuitBreaker.state = 'open';
          this.metrics.circuitBreakerTrips++;
        }
      }
    }
  }

  /**
   * Update gateway health based on request success/failure
   */
  private updateGatewayHealth(gatewayId: string, success: boolean, responseTime: number): void {
    const gateway = this.gateways.get(gatewayId);
    if (!gateway) return;

    if (success) {
      gateway.successRate = Math.min(1.0, gateway.successRate + 0.05);
      gateway.errorRate = Math.max(0, gateway.errorRate - 0.05);
      gateway.responseTime = (gateway.responseTime + responseTime) / 2;
      
      if (gateway.status === 'unhealthy' && gateway.successRate > 0.7) {
        gateway.status = 'degraded';
      } else if (gateway.status === 'degraded' && gateway.successRate > 0.9) {
        gateway.status = 'healthy';
      }
    } else {
      gateway.errorRate = Math.min(1.0, gateway.errorRate + 0.1);
      gateway.successRate = Math.max(0, gateway.successRate - 0.1);
      
      if (gateway.status === 'healthy' && gateway.errorRate > 0.3) {
        gateway.status = 'degraded';
      } else if (gateway.status === 'degraded' && gateway.errorRate > 0.5) {
        gateway.status = 'unhealthy';
      }
    }
  }

  /**
   * Update metrics
   */
  private updateMetrics(success: boolean, responseTime: number, bytesTransferred: number): void {
    if (success) {
      this.metrics.successfulRequests++;
    } else {
      this.metrics.failedRequests++;
    }

    this.metrics.averageResponseTime = 
      (this.metrics.averageResponseTime + responseTime) / 2;
    
    this.metrics.totalBytesTransferred += bytesTransferred;
  }

  /**
   * Check if cached content is still valid
   */
  private isCacheValid(cached: any): boolean {
    return Date.now() - cached.timestamp < cached.ttl;
  }

  /**
   * Get current metrics
   */
  getMetrics(): IPFSMetrics {
    return { ...this.metrics };
  }

  /**
   * Get replication information for a specific CID
   */
  getReplicationInfo(cid: string): ReplicationInfo | null {
    return this.replicationTracker.get(cid) || null;
  }

  /**
   * Get gateway status
   */
  getGatewayStatus(): IPFSGateway[] {
    return Array.from(this.gateways.values());
  }

  /**
   * Cleanup resources
   */
  destroy(): void {
    if (this.healthCheckInterval) {
      clearInterval(this.healthCheckInterval);
    }
    
    this.removeAllListeners();
    this.contentCache.clear();
    this.replicationTracker.clear();
    this.circuitBreakers.clear();
  }
}

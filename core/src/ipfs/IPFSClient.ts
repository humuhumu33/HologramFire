/**
 * IPFS Client for Hologram Distributed Storage
 * 
 * Implements IPFS integration for decentralized content distribution
 * and discovery, providing the primary distribution mechanism for
 * the Hologram system.
 */

import { create, IPFSHTTPClient } from 'ipfs-http-client';
import { CID } from 'ipfs-http-client';
import { Content, Atlas12288Metadata } from '../graphql/types';
import { Atlas12288Encoder } from '../atlas12288/Atlas12288Encoder';

export interface IPFSConfig {
  host: string;
  port: number;
  protocol: string;
  timeout: number;
  retries: number;
}

export interface IPFSContent {
  cid: string;
  content: Content;
  atlasMetadata: Atlas12288Metadata;
  replicationFactor: number;
  lastUpdated: string;
}

export class IPFSClient {
  private client: IPFSHTTPClient;
  private config: IPFSConfig;
  private atlasEncoder: Atlas12288Encoder;
  private contentCache: Map<string, IPFSContent>;

  constructor(config: IPFSConfig) {
    this.config = config;
    this.atlasEncoder = new Atlas12288Encoder();
    this.contentCache = new Map();
    
    // Initialize IPFS client
    this.client = create({
      host: config.host,
      port: config.port,
      protocol: config.protocol,
      timeout: config.timeout
    });
  }

  /**
   * Store content in IPFS with atlas-12288 encoding
   */
  async storeContent(content: Content): Promise<string> {
    try {
      // Encode content to atlas-12288 format
      const atlasMetadata = await this.atlasEncoder.encodeContent({
        name: content.name,
        data: content.data,
        mimeType: content.metadata.mimeType || 'application/octet-stream'
      });

      // Create IPFS content object
      const ipfsContent = {
        content,
        atlasMetadata,
        witness: content.witness,
        metadata: content.metadata
      };

      // Add content to IPFS
      const result = await this.client.add(JSON.stringify(ipfsContent), {
        pin: true,
        cidVersion: 1
      });

      const cid = result.cid.toString();
      
      // Store in cache
      this.contentCache.set(cid, {
        cid,
        content,
        atlasMetadata,
        replicationFactor: 1, // Will be updated by IPFS
        lastUpdated: new Date().toISOString()
      });

      console.log(`✅ Content stored in IPFS with CID: ${cid}`);
      return cid;
    } catch (error) {
      console.error('Failed to store content in IPFS:', error);
      throw error;
    }
  }

  /**
   * Retrieve content from IPFS by CID
   */
  async getContent(cid: string): Promise<Content | null> {
    try {
      // Check cache first
      const cached = this.contentCache.get(cid);
      if (cached) {
        return cached.content;
      }

      // Retrieve from IPFS
      const chunks: Uint8Array[] = [];
      for await (const chunk of this.client.cat(cid)) {
        chunks.push(chunk);
      }

      // Combine chunks
      const totalLength = chunks.reduce((acc, chunk) => acc + chunk.length, 0);
      const combined = new Uint8Array(totalLength);
      let offset = 0;
      for (const chunk of chunks) {
        combined.set(chunk, offset);
        offset += chunk.length;
      }

      // Parse content
      const contentString = new TextDecoder().decode(combined);
      const ipfsContent = JSON.parse(contentString);

      // Validate content structure
      if (!this.validateIPFSContent(ipfsContent)) {
        throw new Error('Invalid IPFS content structure');
      }

      // Store in cache
      this.contentCache.set(cid, {
        cid,
        content: ipfsContent.content,
        atlasMetadata: ipfsContent.atlasMetadata,
        replicationFactor: 1,
        lastUpdated: new Date().toISOString()
      });

      return ipfsContent.content;
    } catch (error) {
      console.error(`Failed to retrieve content from IPFS (CID: ${cid}):`, error);
      return null;
    }
  }

  /**
   * Store content by UOR-ID
   */
  async storeByUORID(uorId: string, content: Content): Promise<string> {
    try {
      // Store content in IPFS
      const cid = await this.storeContent(content);
      
      // Create UOR-ID to CID mapping
      const mapping = {
        uorId,
        cid,
        timestamp: Date.now()
      };

      // Store mapping in IPFS
      const mappingResult = await this.client.add(JSON.stringify(mapping), {
        pin: true,
        cidVersion: 1
      });

      console.log(`✅ UOR-ID mapping stored: ${uorId} -> ${cid}`);
      return cid;
    } catch (error) {
      console.error(`Failed to store content by UOR-ID: ${uorId}`, error);
      throw error;
    }
  }

  /**
   * Retrieve content by UOR-ID
   */
  async getByUORID(uorId: string): Promise<Content | null> {
    try {
      // Generate mapping CID from UOR-ID
      const mappingCid = await this.generateMappingCID(uorId);
      
      // Retrieve mapping
      const mapping = await this.getMapping(mappingCid);
      if (!mapping) {
        return null;
      }

      // Retrieve content by CID
      return await this.getContent(mapping.cid);
    } catch (error) {
      console.error(`Failed to retrieve content by UOR-ID: ${uorId}`, error);
      return null;
    }
  }

  /**
   * Store content by atlas-12288 coordinates
   */
  async storeByCoordinates(page: number, cycle: number, content: Content): Promise<string> {
    try {
      // Store content in IPFS
      const cid = await this.storeContent(content);
      
      // Create coordinate to CID mapping
      const mapping = {
        coordinates: { page, cycle },
        cid,
        timestamp: Date.now()
      };

      // Store mapping in IPFS
      const mappingResult = await this.client.add(JSON.stringify(mapping), {
        pin: true,
        cidVersion: 1
      });

      console.log(`✅ Coordinate mapping stored: (${page}, ${cycle}) -> ${cid}`);
      return cid;
    } catch (error) {
      console.error(`Failed to store content by coordinates: (${page}, ${cycle})`, error);
      throw error;
    }
  }

  /**
   * Retrieve content by atlas-12288 coordinates
   */
  async getByCoordinates(page: number, cycle: number): Promise<Content | null> {
    try {
      // Generate mapping CID from coordinates
      const mappingCid = await this.generateCoordinateMappingCID(page, cycle);
      
      // Retrieve mapping
      const mapping = await this.getMapping(mappingCid);
      if (!mapping) {
        return null;
      }

      // Retrieve content by CID
      return await this.getContent(mapping.cid);
    } catch (error) {
      console.error(`Failed to retrieve content by coordinates: (${page}, ${cycle})`, error);
      return null;
    }
  }

  /**
   * Search content by metadata
   */
  async searchContent(criteria: {
    mimeType?: string;
    r96Class?: number;
    page?: number;
    cycle?: number;
    limit?: number;
  }): Promise<Content[]> {
    try {
      const results: Content[] = [];
      
      // In a real implementation, this would use IPFS search capabilities
      // For now, we'll search through cached content
      for (const [cid, ipfsContent] of this.contentCache) {
        const content = ipfsContent.content;
        
        // Apply filters
        if (criteria.mimeType && content.metadata.mimeType !== criteria.mimeType) {
          continue;
        }
        
        if (criteria.r96Class !== undefined && 
            content.metadata.atlas12288.r96Class !== criteria.r96Class) {
          continue;
        }
        
        if (criteria.page !== undefined && 
            content.metadata.atlas12288.page !== criteria.page) {
          continue;
        }
        
        if (criteria.cycle !== undefined && 
            content.metadata.atlas12288.cycle !== criteria.cycle) {
          continue;
        }
        
        results.push(content);
        
        // Apply limit
        if (criteria.limit && results.length >= criteria.limit) {
          break;
        }
      }
      
      return results;
    } catch (error) {
      console.error('Failed to search content:', error);
      return [];
    }
  }

  /**
   * Pin content to ensure availability
   */
  async pinContent(cid: string): Promise<void> {
    try {
      await this.client.pin.add(cid);
      console.log(`✅ Content pinned: ${cid}`);
    } catch (error) {
      console.error(`Failed to pin content: ${cid}`, error);
      throw error;
    }
  }

  /**
   * Unpin content
   */
  async unpinContent(cid: string): Promise<void> {
    try {
      await this.client.pin.rm(cid);
      console.log(`✅ Content unpinned: ${cid}`);
    } catch (error) {
      console.error(`Failed to unpin content: ${cid}`, error);
      throw error;
    }
  }

  /**
   * Get content statistics
   */
  async getContentStats(): Promise<{
    totalContent: number;
    totalSize: number;
    averageReplicationFactor: number;
    pinnedContent: number;
  }> {
    try {
      const pinned = await this.client.pin.ls();
      let pinnedCount = 0;
      for await (const _ of pinned) {
        pinnedCount++;
      }
      
      let totalSize = 0;
      let totalReplicationFactor = 0;
      
      for (const [cid, ipfsContent] of this.contentCache) {
        totalSize += ipfsContent.content.metadata.size;
        totalReplicationFactor += ipfsContent.replicationFactor;
      }
      
      const averageReplicationFactor = this.contentCache.size > 0 
        ? totalReplicationFactor / this.contentCache.size 
        : 0;
      
      return {
        totalContent: this.contentCache.size,
        totalSize,
        averageReplicationFactor,
        pinnedContent: pinnedCount
      };
    } catch (error) {
      console.error('Failed to get content stats:', error);
      return {
        totalContent: 0,
        totalSize: 0,
        averageReplicationFactor: 0,
        pinnedContent: 0
      };
    }
  }

  /**
   * Generate mapping CID from UOR-ID
   */
  private async generateMappingCID(uorId: string): Promise<string> {
    // In a real implementation, this would use a deterministic method
    // to generate CIDs from UOR-IDs
    const input = `uor_mapping:${uorId}`;
    const result = await this.client.add(input, { cidVersion: 1 });
    return result.cid.toString();
  }

  /**
   * Generate coordinate mapping CID
   */
  private async generateCoordinateMappingCID(page: number, cycle: number): Promise<string> {
    // In a real implementation, this would use a deterministic method
    // to generate CIDs from coordinates
    const input = `coordinate_mapping:${page}:${cycle}`;
    const result = await this.client.add(input, { cidVersion: 1 });
    return result.cid.toString();
  }

  /**
   * Get mapping from IPFS
   */
  private async getMapping(mappingCid: string): Promise<any> {
    try {
      const chunks: Uint8Array[] = [];
      for await (const chunk of this.client.cat(mappingCid)) {
        chunks.push(chunk);
      }

      const totalLength = chunks.reduce((acc, chunk) => acc + chunk.length, 0);
      const combined = new Uint8Array(totalLength);
      let offset = 0;
      for (const chunk of chunks) {
        combined.set(chunk, offset);
        offset += chunk.length;
      }

      const mappingString = new TextDecoder().decode(combined);
      return JSON.parse(mappingString);
    } catch (error) {
      console.error(`Failed to get mapping: ${mappingCid}`, error);
      return null;
    }
  }

  /**
   * Validate IPFS content structure
   */
  private validateIPFSContent(content: any): boolean {
    return (
      content &&
      content.content &&
      content.atlasMetadata &&
      content.content.id &&
      content.content.name &&
      content.content.data &&
      content.content.metadata
    );
  }

  /**
   * Close IPFS client
   */
  async close(): Promise<void> {
    try {
      // IPFS client doesn't have a close method, but we can clear cache
      this.contentCache.clear();
      console.log('✅ IPFS client closed');
    } catch (error) {
      console.error('Failed to close IPFS client:', error);
      throw error;
    }
  }
}

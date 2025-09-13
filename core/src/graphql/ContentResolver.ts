/**
 * Content Resolver for GraphQL Content Resolution System
 * 
 * Implements the core content resolution logic that leverages
 * the bijective properties of atlas-12288 for deterministic content addressing.
 */

import { Content, SearchCriteria, ResolutionStats } from './types';
import { Atlas12288Encoder } from '../atlas12288/Atlas12288Encoder';
import { ConservationVerifier } from '../conservation/ConservationVerifier';

export class ContentResolver {
  private atlasEncoder: Atlas12288Encoder;
  private conservationVerifier: ConservationVerifier;
  private contentStore: Map<string, Content>;
  private nameToUORID: Map<string, string>;
  private coordinateToUORID: Map<string, string>;
  private resolutionStats: {
    totalContent: number;
    totalResolutions: number;
    totalResolutionTime: number;
    conservationViolations: number;
  };

  constructor() {
    this.atlasEncoder = new Atlas12288Encoder();
    this.conservationVerifier = new ConservationVerifier();
    this.contentStore = new Map();
    this.nameToUORID = new Map();
    this.coordinateToUORID = new Map();
    this.resolutionStats = {
      totalContent: 0,
      totalResolutions: 0,
      totalResolutionTime: 0,
      conservationViolations: 0
    };
  }

  /**
   * Resolve content by name using bijective mapping
   */
  async resolveByName(name: string): Promise<Content | null> {
    const startTime = Date.now();
    
    try {
      // Use bijective mapping to get UOR-ID from name
      const uorId = this.nameToUORID.get(name);
      if (!uorId) {
        return null;
      }

      // Get content by UOR-ID
      const content = this.contentStore.get(uorId);
      if (!content) {
        return null;
      }

      // Verify bijective mapping integrity
      const expectedUORID = await this.atlasEncoder.generateUORID({
        name: content.name,
        data: content.data,
        mimeType: content.metadata.mimeType || 'application/octet-stream'
      });

      if (expectedUORID !== uorId) {
        throw new Error(`Bijective mapping violation: name "${name}" maps to incorrect UOR-ID`);
      }

      // Update resolution statistics
      this.updateResolutionStats(Date.now() - startTime);

      return content;
    } catch (error) {
      console.error(`Failed to resolve content by name: ${name}`, error);
      this.resolutionStats.conservationViolations++;
      return null;
    }
  }

  /**
   * Resolve content by UOR-ID
   */
  async resolveByUORID(uorId: string): Promise<Content | null> {
    const startTime = Date.now();
    
    try {
      const content = this.contentStore.get(uorId);
      if (!content) {
        return null;
      }

      // Verify UOR-ID integrity
      const expectedUORID = await this.atlasEncoder.generateUORID({
        name: content.name,
        data: content.data,
        mimeType: content.metadata.mimeType || 'application/octet-stream'
      });

      if (expectedUORID !== uorId) {
        throw new Error(`UOR-ID integrity violation: content does not match UOR-ID ${uorId}`);
      }

      // Update resolution statistics
      this.updateResolutionStats(Date.now() - startTime);

      return content;
    } catch (error) {
      console.error(`Failed to resolve content by UOR-ID: ${uorId}`, error);
      this.resolutionStats.conservationViolations++;
      return null;
    }
  }

  /**
   * Resolve content by atlas-12288 coordinates
   */
  async resolveByCoordinates(page: number, cycle: number): Promise<Content | null> {
    const startTime = Date.now();
    
    try {
      // Validate coordinates
      if (page < 0 || page >= 48 || cycle < 0 || cycle >= 256) {
        throw new Error(`Invalid coordinates: page=${page}, cycle=${cycle}`);
      }

      const coordinateKey = `${page}:${cycle}`;
      const uorId = this.coordinateToUORID.get(coordinateKey);
      if (!uorId) {
        return null;
      }

      const content = this.contentStore.get(uorId);
      if (!content) {
        return null;
      }

      // Verify coordinate mapping integrity
      const atlasMetadata = await this.atlasEncoder.encodeContent({
        name: content.name,
        data: content.data,
        mimeType: content.metadata.mimeType || 'application/octet-stream'
      });

      if (atlasMetadata.page !== page || atlasMetadata.cycle !== cycle) {
        throw new Error(`Coordinate mapping violation: content does not map to coordinates page=${page}, cycle=${cycle}`);
      }

      // Update resolution statistics
      this.updateResolutionStats(Date.now() - startTime);

      return content;
    } catch (error) {
      console.error(`Failed to resolve content by coordinates: page=${page}, cycle=${cycle}`, error);
      this.resolutionStats.conservationViolations++;
      return null;
    }
  }

  /**
   * Search content by metadata criteria
   */
  async searchContent(criteria: SearchCriteria): Promise<Content[]> {
    const startTime = Date.now();
    
    try {
      const results: Content[] = [];
      let count = 0;
      let offset = 0;

      for (const [uorId, content] of this.contentStore) {
        // Apply filters
        if (criteria.mimeType && content.metadata.mimeType !== criteria.mimeType) {
          continue;
        }

        if (criteria.r96Class !== undefined && content.metadata.atlas12288.r96Class !== criteria.r96Class) {
          continue;
        }

        if (criteria.page !== undefined && content.metadata.atlas12288.page !== criteria.page) {
          continue;
        }

        if (criteria.cycle !== undefined && content.metadata.atlas12288.cycle !== criteria.cycle) {
          continue;
        }

        // Apply offset
        if (offset < criteria.offset) {
          offset++;
          continue;
        }

        // Apply limit
        if (count >= criteria.limit) {
          break;
        }

        results.push(content);
        count++;
      }

      // Update resolution statistics
      this.updateResolutionStats(Date.now() - startTime);

      return results;
    } catch (error) {
      console.error('Failed to search content:', error);
      this.resolutionStats.conservationViolations++;
      return [];
    }
  }

  /**
   * Store content with bijective mapping
   */
  async storeContent(content: Content): Promise<void> {
    try {
      // Verify conservation laws before storing
      const conservationValid = await this.conservationVerifier.verifyContent(content);
      if (!conservationValid) {
        throw new Error('Content violates conservation laws and cannot be stored');
      }

      // Store content
      this.contentStore.set(content.id, content);

      // Update bijective mappings
      this.nameToUORID.set(content.name, content.id);
      
      const coordinateKey = `${content.metadata.atlas12288.page}:${content.metadata.atlas12288.cycle}`;
      this.coordinateToUORID.set(coordinateKey, content.id);

      // Update statistics
      this.resolutionStats.totalContent++;

    } catch (error) {
      console.error('Failed to store content:', error);
      throw error;
    }
  }

  /**
   * Update content while maintaining bijective mapping
   */
  async updateContent(content: Content): Promise<void> {
    try {
      // Get existing content
      const existingContent = this.contentStore.get(content.id);
      if (!existingContent) {
        throw new Error(`Content not found: ${content.id}`);
      }

      // Verify conservation laws for updated content
      const conservationValid = await this.conservationVerifier.verifyContent(content);
      if (!conservationValid) {
        throw new Error('Updated content violates conservation laws');
      }

      // Update content
      this.contentStore.set(content.id, content);

      // Update bijective mappings if coordinates changed
      const oldCoordinateKey = `${existingContent.metadata.atlas12288.page}:${existingContent.metadata.atlas12288.cycle}`;
      const newCoordinateKey = `${content.metadata.atlas12288.page}:${content.metadata.atlas12288.cycle}`;
      
      if (oldCoordinateKey !== newCoordinateKey) {
        this.coordinateToUORID.delete(oldCoordinateKey);
        this.coordinateToUORID.set(newCoordinateKey, content.id);
      }

    } catch (error) {
      console.error('Failed to update content:', error);
      throw error;
    }
  }

  /**
   * Delete content and clean up bijective mappings
   */
  async deleteContent(uorId: string): Promise<void> {
    try {
      const content = this.contentStore.get(uorId);
      if (!content) {
        return;
      }

      // Remove from content store
      this.contentStore.delete(uorId);

      // Clean up bijective mappings
      this.nameToUORID.delete(content.name);
      
      const coordinateKey = `${content.metadata.atlas12288.page}:${content.metadata.atlas12288.cycle}`;
      this.coordinateToUORID.delete(coordinateKey);

      // Update statistics
      this.resolutionStats.totalContent--;

    } catch (error) {
      console.error('Failed to delete content:', error);
      throw error;
    }
  }

  /**
   * Get resolution statistics
   */
  async getResolutionStats(): Promise<ResolutionStats> {
    const averageResolutionTime = this.resolutionStats.totalResolutions > 0 
      ? this.resolutionStats.totalResolutionTime / this.resolutionStats.totalResolutions 
      : 0;

    const bijectionIntegrity = this.calculateBijectionIntegrity();

    return {
      totalContent: this.resolutionStats.totalContent,
      totalResolutions: this.resolutionStats.totalResolutions,
      averageResolutionTime,
      conservationViolations: this.resolutionStats.conservationViolations,
      bijectionIntegrity
    };
  }

  /**
   * Update resolution statistics
   */
  private updateResolutionStats(resolutionTime: number): void {
    this.resolutionStats.totalResolutions++;
    this.resolutionStats.totalResolutionTime += resolutionTime;
  }

  /**
   * Calculate bijection integrity score
   */
  private calculateBijectionIntegrity(): number {
    if (this.resolutionStats.totalContent === 0) {
      return 1.0;
    }

    const violations = this.resolutionStats.conservationViolations;
    const total = this.resolutionStats.totalResolutions;
    
    if (total === 0) {
      return 1.0;
    }

    return Math.max(0, 1 - (violations / total));
  }
}

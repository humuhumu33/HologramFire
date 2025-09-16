/**
 * Atlas-12288 Demo Engine
 * 
 * Core engine for demonstrating Atlas functionality:
 * - R96 classification (96 equivalence classes)
 * - 48×256 coordinate mapping (12,288 total coordinates)
 * - Deterministic data processing
 */

import { createHash } from 'crypto';

export interface ContentInput {
  name: string;
  data: string;
  mimeType: string;
}

export interface AtlasMetadata {
  page: number;        // 0-47 (48 pages)
  cycle: number;       // 0-255 (256 cycles)
  r96Class: number;    // 0-95 (96 classes)
  kleinWindow: number; // Klein window selection
  conservationHash: string;
  uorId: string;
}

export interface DemoResult {
  input: ContentInput;
  atlas: AtlasMetadata;
  processingTime: number;
  byteAnalysis: {
    totalBytes: number;
    uniqueBytes: number;
    entropy: number;
    r96Classification: number;
  };
}

export class AtlasDemoEngine {
  private readonly N = 12288; // Total elements
  private readonly P = 48;    // Pages (rows)
  private readonly C = 256;   // Cycles (columns)
  private readonly R = 96;    // R96 classes

  /**
   * Process content through Atlas system
   */
  async processContent(content: ContentInput): Promise<DemoResult> {
    const startTime = Date.now();
    
    // Generate Atlas metadata
    const atlas = await this.encodeContent(content);
    
    // Analyze byte content
    const byteAnalysis = this.analyzeBytes(content.data);
    
    const processingTime = Date.now() - startTime;
    
    return {
      input: content,
      atlas,
      processingTime,
      byteAnalysis
    };
  }

  /**
   * Encode content to atlas-12288 format
   */
  private async encodeContent(content: ContentInput): Promise<AtlasMetadata> {
    // Generate deterministic coordinates
    const coordinates = this.generateCoordinates(content);
    
    // Classify content using R96
    const r96Class = this.classifyContent(content);
    
    // Select Klein window
    const kleinWindow = this.selectKleinWindow(content);
    
    // Generate conservation hash
    const conservationHash = this.generateConservationHash(content, coordinates);
    
    // Generate UOR-ID
    const uorId = this.generateUORID(content, coordinates, r96Class);

    return {
      page: coordinates.page,
      cycle: coordinates.cycle,
      r96Class,
      kleinWindow,
      conservationHash,
      uorId
    };
  }

    /**
     * Generate deterministic coordinates for content
     */
    generateCoordinates(content: ContentInput): { page: number; cycle: number } {
    // Use content hash to generate deterministic coordinates
    const contentHash = createHash('sha256').update(content.data).digest('hex');
    const hashBytes = Buffer.from(contentHash, 'hex');
    
    // Generate page (0-47)
    const pageHash = hashBytes.readUInt32BE(0);
    const page = pageHash % this.P;
    
    // Generate cycle (0-255)
    const cycleHash = hashBytes.readUInt32BE(4);
    const cycle = cycleHash % this.C;
    
    return { page, cycle };
  }

    /**
     * Classify content using R96 (96 equivalence classes)
     */
    classifyContent(content: ContentInput): number {
    // Convert content data to byte array for R96 classification
    const dataBytes = Buffer.from(content.data, 'utf8');
    const byteArray = Array.from(dataBytes);
    
    // R96 classification: sum elements modulo 96
    let acc = 0;
    for (const v of byteArray) {
      acc = (acc + (v | 0)) % this.R;
    }
    
    return (acc + this.R) % this.R;
  }

    /**
     * Select Klein window based on content
     */
    selectKleinWindow(content: ContentInput): number {
    const hash = createHash('sha256').update(content.data).digest('hex');
    const hashBytes = Buffer.from(hash, 'hex');
    return hashBytes.readUInt32BE(8) % 192; // 192 Klein windows
  }

  /**
   * Generate conservation hash
   */
  private generateConservationHash(content: ContentInput, coordinates: { page: number; cycle: number }): string {
    const input = `${content.data}:${coordinates.page}:${coordinates.cycle}`;
    return createHash('sha256').update(input).digest('hex').substring(0, 16);
  }

  /**
   * Generate UOR-ID from content and metadata
   */
  private generateUORID(content: ContentInput, coordinates: { page: number; cycle: number }, r96Class: number): string {
    const input = `${content.name}:${content.data}:${coordinates.page}:${coordinates.cycle}:${r96Class}`;
    return createHash('sha256').update(input).digest('hex').substring(0, 32);
  }

    /**
     * Analyze byte content for demo visualization
     */
    analyzeBytes(data: string): {
    totalBytes: number;
    uniqueBytes: number;
    entropy: number;
    r96Classification: number;
  } {
    const bytes = Buffer.from(data, 'utf8');
    const byteArray = Array.from(bytes);
    
    // Count unique bytes
    const uniqueBytes = new Set(byteArray).size;
    
    // Calculate entropy
    const byteCounts = new Map<number, number>();
    for (const byte of byteArray) {
      byteCounts.set(byte, (byteCounts.get(byte) || 0) + 1);
    }
    
    let entropy = 0;
    const totalBytes = byteArray.length;
    for (const count of byteCounts.values()) {
      const probability = count / totalBytes;
      entropy -= probability * Math.log2(probability);
    }
    
    // R96 classification
    let acc = 0;
    for (const v of byteArray) {
      acc = (acc + (v | 0)) % this.R;
    }
    const r96Classification = (acc + this.R) % this.R;
    
    return {
      totalBytes,
      uniqueBytes,
      entropy,
      r96Classification
    };
  }

  /**
   * Generate demo data sets
   */
  generateDemoData(): ContentInput[] {
    return [
      {
        name: "Simple Text",
        data: "Hello, Atlas World!",
        mimeType: "text/plain"
      },
      {
        name: "JSON Data",
        data: JSON.stringify({
          id: 1,
          name: "Demo User",
          email: "demo@atlas.com",
          active: true,
          metadata: {
            created: "2024-01-01",
            version: "1.0.0"
          }
        }),
        mimeType: "application/json"
      },
      {
        name: "Long Text",
        data: "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat.",
        mimeType: "text/plain"
      },
      {
        name: "Binary-like Data",
        data: Buffer.from([0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x57, 0x6F, 0x72, 0x6C, 0x64]).toString('utf8'),
        mimeType: "application/octet-stream"
      },
      {
        name: "Unicode Text",
        data: "🌍 Atlas-12288 世界地图 🗺️",
        mimeType: "text/plain"
      }
    ];
  }

  /**
   * Verify deterministic mapping
   */
  async verifyDeterministicMapping(content: ContentInput, iterations: number = 5): Promise<{
    isDeterministic: boolean;
    results: AtlasMetadata[];
    consistency: number;
  }> {
    const results: AtlasMetadata[] = [];
    
    for (let i = 0; i < iterations; i++) {
      const result = await this.encodeContent(content);
      results.push(result);
    }
    
    // Check if all results are identical
    const firstResult = results[0];
    const isDeterministic = results.every(result => 
      result.page === firstResult.page &&
      result.cycle === firstResult.cycle &&
      result.r96Class === firstResult.r96Class &&
      result.conservationHash === firstResult.conservationHash &&
      result.uorId === firstResult.uorId
    );
    
    const consistency = isDeterministic ? 100 : 0;
    
    return {
      isDeterministic,
      results,
      consistency
    };
  }

  /**
   * Get grid statistics
   */
  getGridStatistics(): {
    totalCoordinates: number;
    pages: number;
    cycles: number;
    r96Classes: number;
    gridDimensions: string;
  } {
    return {
      totalCoordinates: this.N,
      pages: this.P,
      cycles: this.C,
      r96Classes: this.R,
      gridDimensions: `${this.P}×${this.C}`
    };
  }
}

import { HologramOracle, OracleResult } from "./HologramOracle";
import fs from "node:fs";
import path from "node:path";

/**
 * OracleMiddleware - Ensures all new hologram and data functions maintain coherence
 * with hologram_generator_mini as the source of truth.
 * 
 * This middleware automatically validates any new code additions to ensure
 * they maintain holographic correspondence and system coherence.
 */
export class OracleMiddleware {
  private oracle: HologramOracle;
  private validationCache: Map<string, OracleResult> = new Map();

  constructor() {
    this.oracle = new HologramOracle();
  }

  /**
   * Validates a new hologram function before it's added to the system
   */
  validateHologramFunction(functionCode: string, functionName: string): OracleResult {
    const cacheKey = `hologram_${functionName}`;
    
    // Check cache first
    if (this.validationCache.has(cacheKey)) {
      return this.validationCache.get(cacheKey)!;
    }

    // Validate holographic correspondence
    const result = this.validateHolographicCorrespondence(functionCode, functionName);
    
    // Cache the result
    this.validationCache.set(cacheKey, result);
    
    return result;
  }

  /**
   * Validates a new data function before it's added to the system
   */
  validateDataFunction(functionCode: string, functionName: string): OracleResult {
    const cacheKey = `data_${functionName}`;
    
    // Check cache first
    if (this.validationCache.has(cacheKey)) {
      return this.validationCache.get(cacheKey)!;
    }

    // Validate data coherence
    const result = this.validateDataCoherence(functionCode, functionName);
    
    // Cache the result
    this.validationCache.set(cacheKey, result);
    
    return result;
  }

  /**
   * Validates any new module or blueprint addition
   */
  validateNewAddition(filePath: string): OracleResult {
    const cacheKey = `file_${filePath}`;
    
    // Check cache first
    if (this.validationCache.has(cacheKey)) {
      return this.validationCache.get(cacheKey)!;
    }

    let result: OracleResult;

    if (filePath.includes('blueprint')) {
      result = this.oracle.validateBlueprint(filePath);
    } else if (filePath.includes('modules') || filePath.endsWith('.json')) {
      result = this.oracle.validateModule(filePath);
    } else {
      // For other files, perform basic coherence check
      result = this.validateFileCoherence(filePath);
    }

    // Cache the result
    this.validationCache.set(cacheKey, result);
    
    return result;
  }

  /**
   * Validates holographic correspondence for new functions
   */
  private validateHolographicCorrespondence(functionCode: string, functionName: string): OracleResult {
    const violations = [];
    let oracle_score = 1.0;

    // Check for holographic correspondence patterns
    if (!this.hasHolographicPatterns(functionCode)) {
      violations.push({
        type: 'holographic_correspondence' as const,
        severity: 'critical' as const,
        message: `Function ${functionName} must maintain holographic correspondence patterns`,
        location: functionName,
        expected: 'Holographic correspondence patterns',
        actual: 'Missing holographic patterns'
      });
      oracle_score = 0;
    }

    // Check for resonance classification
    if (!this.hasResonanceClassification(functionCode)) {
      violations.push({
        type: 'resonance_mismatch' as const,
        severity: 'warning' as const,
        message: `Function ${functionName} should include resonance classification`,
        location: functionName
      });
      oracle_score *= 0.9;
    }

    // Check for cycle conservation
    if (!this.hasCycleConservation(functionCode)) {
      violations.push({
        type: 'cycle_violation' as const,
        severity: 'warning' as const,
        message: `Function ${functionName} should maintain cycle conservation`,
        location: functionName
      });
      oracle_score *= 0.9;
    }

    // Check for page conservation
    if (!this.hasPageConservation(functionCode)) {
      violations.push({
        type: 'page_conservation' as const,
        severity: 'warning' as const,
        message: `Function ${functionName} should maintain page conservation`,
        location: functionName
      });
      oracle_score *= 0.9;
    }

    return {
      ok: oracle_score >= 0.95,
      oracle_score,
      violations,
      holographic_fingerprint: this.generateFunctionFingerprint(functionCode, functionName)
    };
  }

  /**
   * Validates data coherence for new data functions
   */
  private validateDataCoherence(functionCode: string, functionName: string): OracleResult {
    const violations = [];
    let oracle_score = 1.0;

    // Check for data integrity patterns
    if (!this.hasDataIntegrityPatterns(functionCode)) {
      violations.push({
        type: 'holographic_correspondence' as const,
        severity: 'critical' as const,
        message: `Data function ${functionName} must maintain data integrity patterns`,
        location: functionName,
        expected: 'Data integrity patterns',
        actual: 'Missing data integrity patterns'
      });
      oracle_score = 0;
    }

    // Check for holographic data correspondence
    if (!this.hasHolographicDataCorrespondence(functionCode)) {
      violations.push({
        type: 'holographic_correspondence' as const,
        severity: 'warning' as const,
        message: `Data function ${functionName} should maintain holographic data correspondence`,
        location: functionName
      });
      oracle_score *= 0.8;
    }

    return {
      ok: oracle_score >= 0.95,
      oracle_score,
      violations,
      holographic_fingerprint: this.generateFunctionFingerprint(functionCode, functionName)
    };
  }

  /**
   * Validates file coherence for any new file
   */
  private validateFileCoherence(filePath: string): OracleResult {
    const violations = [];
    let oracle_score = 1.0;

    try {
      const content = fs.readFileSync(filePath, 'utf8');
      
      // Check for holographic patterns in file content
      if (!this.hasHolographicPatterns(content)) {
        violations.push({
          type: 'holographic_correspondence' as const,
          severity: 'warning' as const,
          message: `File ${filePath} should maintain holographic correspondence`,
          location: filePath
        });
        oracle_score *= 0.9;
      }

      // Check for proper file structure
      if (!this.hasProperFileStructure(content, filePath)) {
        violations.push({
          type: 'holographic_correspondence' as const,
          severity: 'info' as const,
          message: `File ${filePath} could benefit from better holographic structure`,
          location: filePath
        });
        oracle_score *= 0.95;
      }

    } catch (error) {
      violations.push({
        type: 'holographic_correspondence' as const,
        severity: 'critical' as const,
        message: `Failed to read file ${filePath}: ${error instanceof Error ? error.message : String(error)}`,
        location: filePath
      });
      oracle_score = 0;
    }

    return {
      ok: oracle_score >= 0.95,
      oracle_score,
      violations,
      holographic_fingerprint: this.generateFileFingerprint(filePath)
    };
  }

  /**
   * Checks if code has holographic correspondence patterns
   */
  private hasHolographicPatterns(code: string): boolean {
    // Look for holographic patterns in the code
    const holographicPatterns = [
      'holographic',
      'correspondence',
      'resonance',
      'coherence',
      'oracle',
      'fingerprint',
      'invariant'
    ];

    return holographicPatterns.some(pattern => 
      code.toLowerCase().includes(pattern.toLowerCase())
    );
  }

  /**
   * Checks if code has resonance classification patterns
   */
  private hasResonanceClassification(code: string): boolean {
    const resonancePatterns = [
      'resonance',
      'frequency',
      'harmonic',
      'oscillation',
      'vibration'
    ];

    return resonancePatterns.some(pattern => 
      code.toLowerCase().includes(pattern.toLowerCase())
    );
  }

  /**
   * Checks if code has cycle conservation patterns
   */
  private hasCycleConservation(code: string): boolean {
    const cyclePatterns = [
      'cycle',
      'conservation',
      'energy',
      'efficiency',
      'optimization'
    ];

    return cyclePatterns.some(pattern => 
      code.toLowerCase().includes(pattern.toLowerCase())
    );
  }

  /**
   * Checks if code has page conservation patterns
   */
  private hasPageConservation(code: string): boolean {
    const pagePatterns = [
      'page',
      'memory',
      'storage',
      'allocation',
      'management'
    ];

    return pagePatterns.some(pattern => 
      code.toLowerCase().includes(pattern.toLowerCase())
    );
  }

  /**
   * Checks if code has data integrity patterns
   */
  private hasDataIntegrityPatterns(code: string): boolean {
    const dataPatterns = [
      'validation',
      'integrity',
      'consistency',
      'checksum',
      'hash',
      'verify'
    ];

    return dataPatterns.some(pattern => 
      code.toLowerCase().includes(pattern.toLowerCase())
    );
  }

  /**
   * Checks if code has holographic data correspondence
   */
  private hasHolographicDataCorrespondence(code: string): boolean {
    const holographicDataPatterns = [
      'holographic',
      'correspondence',
      'oracle',
      'coherence',
      'fingerprint'
    ];

    return holographicDataPatterns.some(pattern => 
      code.toLowerCase().includes(pattern.toLowerCase())
    );
  }

  /**
   * Checks if file has proper holographic structure
   */
  private hasProperFileStructure(content: string, filePath: string): boolean {
    // Check for proper imports and structure
    if (filePath.endsWith('.ts') || filePath.endsWith('.js')) {
      return content.includes('import') || content.includes('require');
    }
    
    if (filePath.endsWith('.json')) {
      try {
        JSON.parse(content);
        return true;
      } catch {
        return false;
      }
    }

    return true;
  }

  /**
   * Generates holographic fingerprint for function code
   */
  private generateFunctionFingerprint(code: string, functionName: string): string {
    const crypto = require('node:crypto');
    const combined = `${functionName}:${code}`;
    return crypto.createHash("sha256").update(combined).digest("hex");
  }

  /**
   * Generates holographic fingerprint for file
   */
  private generateFileFingerprint(filePath: string): string {
    const crypto = require('node:crypto');
    try {
      const content = fs.readFileSync(filePath, 'utf8');
      return crypto.createHash("sha256").update(content).digest("hex");
    } catch {
      return crypto.createHash("sha256").update(filePath).digest("hex");
    }
  }

  /**
   * Clears the validation cache
   */
  clearCache(): void {
    this.validationCache.clear();
  }

  /**
   * Gets cache statistics
   */
  getCacheStats(): { size: number; keys: string[] } {
    return {
      size: this.validationCache.size,
      keys: Array.from(this.validationCache.keys())
    };
  }
}

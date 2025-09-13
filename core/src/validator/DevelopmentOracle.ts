import { OracleMiddleware } from "./OracleMiddleware";
import { HologramOracle } from "./HologramOracle";
import fs from "node:fs";
import path from "node:path";

/**
 * DevelopmentOracle - Real-time oracle validation for development
 * 
 * This class provides real-time validation of new hologram and data functions
 * during development to ensure immediate feedback on coherence violations.
 */
export class DevelopmentOracle {
  private middleware: OracleMiddleware;
  private oracle: HologramOracle;
  private watchPaths: string[] = [];
  private validationResults: Map<string, any> = new Map();

  constructor() {
    this.middleware = new OracleMiddleware();
    this.oracle = new HologramOracle();
  }

  /**
   * Validates new hologram function code in real-time
   */
  validateHologramFunction(functionCode: string, functionName: string): {
    valid: boolean;
    score: number;
    violations: any[];
    suggestions: string[];
  } {
    const result = this.middleware.validateHologramFunction(functionCode, functionName);
    
    const suggestions = this.generateSuggestions(result.violations, 'hologram');
    
    return {
      valid: result.ok,
      score: result.oracle_score,
      violations: result.violations,
      suggestions
    };
  }

  /**
   * Validates new data function code in real-time
   */
  validateDataFunction(functionCode: string, functionName: string): {
    valid: boolean;
    score: number;
    violations: any[];
    suggestions: string[];
  } {
    const result = this.middleware.validateDataFunction(functionCode, functionName);
    
    const suggestions = this.generateSuggestions(result.violations, 'data');
    
    return {
      valid: result.ok,
      score: result.oracle_score,
      violations: result.violations,
      suggestions
    };
  }

  /**
   * Validates any new code addition
   */
  validateNewCode(code: string, fileName: string, functionName?: string): {
    valid: boolean;
    score: number;
    violations: any[];
    suggestions: string[];
  } {
    let result;
    
    if (functionName) {
      if (fileName.includes('hologram') || functionName.includes('hologram')) {
        result = this.middleware.validateHologramFunction(code, functionName);
      } else if (fileName.includes('data') || functionName.includes('data')) {
        result = this.middleware.validateDataFunction(code, functionName);
      } else {
        // For function validation without file, use hologram validation as default
        result = this.middleware.validateHologramFunction(code, functionName);
      }
    } else {
      result = this.middleware.validateNewAddition(fileName);
    }
    
    const suggestions = this.generateSuggestions(result.violations, 'general');
    
    return {
      valid: result.ok,
      score: result.oracle_score,
      violations: result.violations,
      suggestions
    };
  }

  /**
   * Generates helpful suggestions based on violations
   */
  private generateSuggestions(violations: any[], type: string): string[] {
    const suggestions: string[] = [];
    
    for (const violation of violations) {
      switch (violation.type) {
        case 'holographic_correspondence':
          if (type === 'hologram') {
            suggestions.push('Add holographic correspondence patterns: include "holographic", "correspondence", or "oracle" keywords');
            suggestions.push('Ensure the function maintains holographic principles with the reference implementation');
          } else if (type === 'data') {
            suggestions.push('Add data integrity patterns: include "validation", "integrity", or "checksum" keywords');
            suggestions.push('Ensure data functions maintain holographic correspondence');
          }
          break;
          
        case 'resonance_mismatch':
          suggestions.push('Add resonance classification: include "resonance", "frequency", or "harmonic" keywords');
          suggestions.push('Consider adding frequency analysis or harmonic patterns');
          break;
          
        case 'cycle_violation':
          suggestions.push('Add cycle conservation: include "cycle", "conservation", or "efficiency" keywords');
          suggestions.push('Consider adding energy efficiency or optimization patterns');
          break;
          
        case 'page_conservation':
          suggestions.push('Add page conservation: include "page", "memory", or "storage" keywords');
          suggestions.push('Consider adding memory management or storage optimization');
          break;
      }
    }
    
    // Add general suggestions
    if (violations.length > 0) {
      suggestions.push('Ensure all new code maintains coherence with hologram_generator_mini');
      suggestions.push('Consider adding oracle validation calls to your functions');
      suggestions.push('Review the holographic correspondence patterns in existing code');
    }
    
    return suggestions;
  }

  /**
   * Provides real-time feedback for code being written
   */
  getRealTimeFeedback(code: string, fileName: string, functionName?: string): {
    status: 'good' | 'warning' | 'error';
    message: string;
    quickFixes: string[];
  } {
    const validation = this.validateNewCode(code, fileName, functionName);
    
    if (validation.valid) {
      return {
        status: 'good',
        message: `✅ Code maintains oracle coherence (${(validation.score * 100).toFixed(1)}%)`,
        quickFixes: []
      };
    } else if (validation.score >= 0.8) {
      return {
        status: 'warning',
        message: `⚠️ Code has minor oracle violations (${(validation.score * 100).toFixed(1)}%)`,
        quickFixes: validation.suggestions.slice(0, 2) // Top 2 suggestions
      };
    } else {
      return {
        status: 'error',
        message: `❌ Code has critical oracle violations (${(validation.score * 100).toFixed(1)}%)`,
        quickFixes: validation.suggestions.slice(0, 3) // Top 3 suggestions
      };
    }
  }

  /**
   * Validates a complete file
   */
  validateFile(filePath: string): {
    valid: boolean;
    score: number;
    violations: any[];
    suggestions: string[];
  } {
    try {
      const content = fs.readFileSync(filePath, 'utf8');
      const result = this.middleware.validateNewAddition(filePath);
      const suggestions = this.generateSuggestions(result.violations, 'file');
      
      return {
        valid: result.ok,
        score: result.oracle_score,
        violations: result.violations,
        suggestions
      };
    } catch (error) {
      return {
        valid: false,
        score: 0,
        violations: [{
          type: 'holographic_correspondence',
          severity: 'critical',
          message: `Failed to read file: ${error instanceof Error ? error.message : String(error)}`,
          location: filePath
        }],
        suggestions: ['Check file path and permissions', 'Ensure file exists and is readable']
      };
    }
  }

  /**
   * Gets oracle compliance report for a directory
   */
  getComplianceReport(directory: string): {
    totalFiles: number;
    compliantFiles: number;
    nonCompliantFiles: string[];
    averageScore: number;
    recommendations: string[];
  } {
    const files = this.getFilesInDirectory(directory);
    let compliantFiles = 0;
    let totalScore = 0;
    const nonCompliantFiles: string[] = [];
    const recommendations: string[] = [];
    
    for (const file of files) {
      const validation = this.validateFile(file);
      totalScore += validation.score;
      
      if (validation.valid) {
        compliantFiles++;
      } else {
        nonCompliantFiles.push(file);
        recommendations.push(...validation.suggestions);
      }
    }
    
    const averageScore = files.length > 0 ? totalScore / files.length : 0;
    
    return {
      totalFiles: files.length,
      compliantFiles,
      nonCompliantFiles,
      averageScore,
      recommendations: [...new Set(recommendations)] // Remove duplicates
    };
  }

  /**
   * Gets all files in a directory recursively
   */
  private getFilesInDirectory(dir: string): string[] {
    const files: string[] = [];
    
    try {
      const items = fs.readdirSync(dir);
      
      for (const item of items) {
        const fullPath = path.join(dir, item);
        const stat = fs.statSync(fullPath);
        
        if (stat.isDirectory()) {
          files.push(...this.getFilesInDirectory(fullPath));
        } else if (stat.isFile() && (item.endsWith('.ts') || item.endsWith('.js') || item.endsWith('.json'))) {
          files.push(fullPath);
        }
      }
    } catch (error) {
      // Directory doesn't exist or can't be read
    }
    
    return files;
  }

  /**
   * Clears validation cache
   */
  clearCache(): void {
    this.middleware.clearCache();
    this.validationResults.clear();
  }

  /**
   * Gets validation statistics
   */
  getStats(): {
    cacheSize: number;
    validationCount: number;
    averageScore: number;
  } {
    const cacheStats = this.middleware.getCacheStats();
    const validationCount = this.validationResults.size;
    
    let totalScore = 0;
    for (const result of this.validationResults.values()) {
      totalScore += result.score || 0;
    }
    const averageScore = validationCount > 0 ? totalScore / validationCount : 0;
    
    return {
      cacheSize: cacheStats.size,
      validationCount,
      averageScore
    };
  }
}

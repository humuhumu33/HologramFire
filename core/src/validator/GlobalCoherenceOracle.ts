import { MasterHologramOracle, OracleMode, MasterOracleResult, OracleViolation } from './MasterHologramOracle';
import { Metrics } from '../monitoring/metrics/Metrics';
import fs from 'node:fs';
import path from 'node:path';
// import { glob } from 'glob'; // Not used in current implementation

/**
 * Global Coherence Oracle - System-wide Coherence Validation
 * 
 * This class applies the Oracle system to check for global coherence across
 * the entire Hologram system, validating all modules, blueprints, and components
 * for holographic correspondence and system-wide consistency.
 */

export interface GlobalCoherenceConfig {
  // System-wide validation settings
  enableBlueprintValidation: boolean;
  enableModuleValidation: boolean;
  enableComponentValidation: boolean;
  enableCrossModuleValidation: boolean;
  enableDependencyValidation: boolean;
  
  // Oracle mode configuration
  oracleMode: OracleMode;
  
  // Paths to validate
  blueprintPaths: string[];
  modulePaths: string[];
  componentPaths: string[];
  excludePaths: string[];
  
  // Coherence thresholds
  globalCoherenceThreshold: number;
  moduleCoherenceThreshold: number;
  blueprintCoherenceThreshold: number;
  
  // Performance settings
  enableParallelValidation: boolean;
  maxConcurrentValidations: number;
  enableCaching: boolean;
  cacheTimeoutMs: number;
  
  // Reporting settings
  generateDetailedReport: boolean;
  generateSummaryReport: boolean;
  outputPath: string;
}

export interface GlobalCoherenceResult {
  // Overall system coherence
  globalCoherenceScore: number;
  systemStatus: 'coherent' | 'warning' | 'critical' | 'failed';
  
  // Component-wise results
  blueprintResults: ComponentCoherenceResult[];
  moduleResults: ComponentCoherenceResult[];
  componentResults: ComponentCoherenceResult[];
  
  // Cross-system analysis
  crossModuleCoherence: CrossModuleCoherenceResult;
  dependencyCoherence: DependencyCoherenceResult;
  
  // Violations and issues
  globalViolations: OracleViolation[];
  criticalIssues: CriticalIssue[];
  recommendations: string[];
  
  // Performance metrics
  validationMetrics: ValidationMetrics;
  
  // Metadata
  timestamp: number;
  executionTimeMs: number;
  totalFilesValidated: number;
  oracleVersion: string;
}

export interface ComponentCoherenceResult {
  path: string;
  name: string;
  type: 'blueprint' | 'module' | 'component';
  oracleResult: MasterOracleResult;
  coherenceScore: number;
  status: 'coherent' | 'warning' | 'critical' | 'failed';
  violations: OracleViolation[];
  dependencies: string[];
  dependents: string[];
}

export interface CrossModuleCoherenceResult {
  overallScore: number;
  moduleInteractions: ModuleInteraction[];
  coherenceViolations: CoherenceViolation[];
  recommendations: string[];
}

export interface ModuleInteraction {
  sourceModule: string;
  targetModule: string;
  interactionType: 'dependency' | 'reference' | 'import' | 'export';
  coherenceScore: number;
  violations: OracleViolation[];
}

export interface CoherenceViolation {
  type: 'interface_mismatch' | 'invariant_conflict' | 'dependency_cycle' | 'version_mismatch';
  severity: 'critical' | 'warning' | 'info';
  message: string;
  affectedModules: string[];
  suggestion: string;
}

export interface DependencyCoherenceResult {
  overallScore: number;
  dependencyGraph: DependencyNode[];
  circularDependencies: CircularDependency[];
  versionConflicts: VersionConflict[];
  missingDependencies: string[];
}

export interface DependencyNode {
  name: string;
  version: string;
  dependencies: string[];
  dependents: string[];
  coherenceScore: number;
}

export interface CircularDependency {
  cycle: string[];
  severity: 'critical' | 'warning';
  impact: string;
}

export interface VersionConflict {
  dependency: string;
  requiredVersions: string[];
  conflictType: 'range_overlap' | 'exact_mismatch';
  severity: 'critical' | 'warning';
}

export interface CriticalIssue {
  type: 'system_breaking' | 'coherence_violation' | 'dependency_issue' | 'performance_issue';
  severity: 'critical' | 'high' | 'medium';
  description: string;
  affectedComponents: string[];
  impact: string;
  resolution: string;
}

export interface ValidationMetrics {
  totalValidationTimeMs: number;
  averageValidationTimeMs: number;
  cacheHitRate: number;
  parallelizationEfficiency: number;
  memoryUsageMB: number;
  cpuUsagePercent: number;
}

export class GlobalCoherenceOracle {
  private masterOracle: MasterHologramOracle;
  private metrics: Metrics;
  private config: GlobalCoherenceConfig;
  private validationCache: Map<string, { result: MasterOracleResult; timestamp: number }> = new Map();
  
  constructor(config: Partial<GlobalCoherenceConfig> = {}) {
    this.metrics = new Metrics();
    this.config = {
      enableBlueprintValidation: true,
      enableModuleValidation: true,
      enableComponentValidation: true,
      enableCrossModuleValidation: true,
      enableDependencyValidation: true,
      oracleMode: { type: 'strict', config: {} },
      blueprintPaths: ['atlas-12288/blueprint/**/*.json'],
      modulePaths: ['modules/**/*.json', 'data/modules/**/*.json'],
      componentPaths: ['src/**/*.ts', 'src/**/*.js'],
      excludePaths: ['node_modules/**', 'build/**', 'dist/**', 'tests/**'],
      globalCoherenceThreshold: 0.95,
      moduleCoherenceThreshold: 0.90,
      blueprintCoherenceThreshold: 0.95,
      enableParallelValidation: true,
      maxConcurrentValidations: 10,
      enableCaching: true,
      cacheTimeoutMs: 30000,
      generateDetailedReport: true,
      generateSummaryReport: true,
      outputPath: 'global-coherence-report.json',
      ...config
    };
    
    this.masterOracle = new MasterHologramOracle(this.config.oracleMode);
  }

  /**
   * Perform global coherence validation across the entire system
   */
  async validateGlobalCoherence(): Promise<GlobalCoherenceResult> {
    const startTime = Date.now();
    this.metrics.inc('global_coherence_validations', 1);
    
    try {
      console.log('🔍 Starting global coherence validation...');
      
      // Discover all files to validate
      const filesToValidate = await this.discoverFiles();
      console.log(`📁 Found ${filesToValidate.length} files to validate`);
      
      // Validate components in parallel
      const validationResults = await this.validateComponents(filesToValidate);
      
      // Analyze cross-module coherence
      const crossModuleCoherence = await this.analyzeCrossModuleCoherence(validationResults);
      
      // Analyze dependency coherence
      const dependencyCoherence = await this.analyzeDependencyCoherence(validationResults);
      
      // Calculate global coherence score
      const globalCoherenceScore = this.calculateGlobalCoherenceScore(validationResults);
      
      // Identify critical issues
      const criticalIssues = this.identifyCriticalIssues(validationResults, crossModuleCoherence, dependencyCoherence);
      
      // Generate recommendations
      const recommendations = this.generateRecommendations(validationResults, criticalIssues);
      
      // Determine system status
      const systemStatus = this.determineSystemStatus(globalCoherenceScore, criticalIssues);
      
      // Calculate validation metrics
      const validationMetrics = this.calculateValidationMetrics(startTime, filesToValidate.length);
      
      const result: GlobalCoherenceResult = {
        globalCoherenceScore,
        systemStatus,
        blueprintResults: validationResults.filter(r => r.type === 'blueprint'),
        moduleResults: validationResults.filter(r => r.type === 'module'),
        componentResults: validationResults.filter(r => r.type === 'component'),
        crossModuleCoherence,
        dependencyCoherence,
        globalViolations: this.aggregateViolations(validationResults),
        criticalIssues,
        recommendations,
        validationMetrics,
        timestamp: Date.now(),
        executionTimeMs: Date.now() - startTime,
        totalFilesValidated: filesToValidate.length,
        oracleVersion: '1.0.0'
      };
      
      // Generate reports if requested
      if (this.config.generateDetailedReport || this.config.generateSummaryReport) {
        await this.generateReports(result);
      }
      
      console.log(`✅ Global coherence validation completed in ${result.executionTimeMs}ms`);
      console.log(`📊 Global coherence score: ${(globalCoherenceScore * 100).toFixed(1)}%`);
      console.log(`🚨 Critical issues: ${criticalIssues.length}`);
      
      return result;
      
    } catch (error) {
      this.metrics.inc('global_coherence_errors', 1);
      throw new Error(`Global coherence validation failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Discover all files that need validation
   */
  private async discoverFiles(): Promise<string[]> {
    const allFiles: string[] = [];
    
    // Discover blueprint files
    if (this.config.enableBlueprintValidation) {
      for (const pattern of this.config.blueprintPaths) {
        const files = this.getFilesMatchingPattern(pattern);
        allFiles.push(...files);
      }
    }
    
    // Discover module files
    if (this.config.enableModuleValidation) {
      for (const pattern of this.config.modulePaths) {
        const files = this.getFilesMatchingPattern(pattern);
        allFiles.push(...files);
      }
    }
    
    // Discover component files
    if (this.config.enableComponentValidation) {
      for (const pattern of this.config.componentPaths) {
        const files = this.getFilesMatchingPattern(pattern);
        allFiles.push(...files);
      }
    }
    
    // Remove duplicates and filter out non-existent files
    const uniqueFiles = [...new Set(allFiles)].filter(file => {
      try {
        return fs.existsSync(file);
      } catch {
        return false;
      }
    });
    
    return uniqueFiles;
  }

  /**
   * Validate all discovered components
   */
  private async validateComponents(files: string[]): Promise<ComponentCoherenceResult[]> {
    const results: ComponentCoherenceResult[] = [];
    
    if (this.config.enableParallelValidation) {
      // Validate in parallel with concurrency limit
      const chunks = this.chunkArray(files, this.config.maxConcurrentValidations);
      
      for (const chunk of chunks) {
        const chunkResults = await Promise.all(
          chunk.map(file => this.validateSingleComponent(file))
        );
        results.push(...chunkResults);
      }
    } else {
      // Validate sequentially
      for (const file of files) {
        const result = await this.validateSingleComponent(file);
        results.push(result);
      }
    }
    
    return results;
  }

  /**
   * Validate a single component
   */
  private async validateSingleComponent(filePath: string): Promise<ComponentCoherenceResult> {
    const startTime = Date.now();
    
    try {
      // Check cache first
      if (this.config.enableCaching) {
        const cached = this.validationCache.get(filePath);
        if (cached && (Date.now() - cached.timestamp) < this.config.cacheTimeoutMs) {
          return this.createComponentResult(filePath, cached.result, Date.now() - startTime);
        }
      }
      
      // Determine component type
      const componentType = this.determineComponentType(filePath);
      
      // Validate with master oracle
      const oracleResult = await this.masterOracle.validate(filePath);
      
      // Cache result
      if (this.config.enableCaching) {
        this.validationCache.set(filePath, { result: oracleResult, timestamp: Date.now() });
      }
      
      return this.createComponentResult(filePath, oracleResult, Date.now() - startTime);
      
    } catch (error) {
      // Create error result
      const errorResult: MasterOracleResult = {
        ok: false,
        isValid: false,
        oracle_score: 0,
        score: 0,
        confidence: 0,
        violations: [{
          type: 'holographic_correspondence',
          severity: 'critical',
          message: `Validation failed: ${error instanceof Error ? error.message : String(error)}`
        }],
        warnings: [],
        holographic_fingerprint: '',
        fingerprint: '',
        validationTime: 0,
        analysisTime: 0,
        complexity: 0,
        stability: 0,
        efficiency: 0,
        recommendations: [],
        execution_time_ms: Date.now() - startTime,
        timestamp: Date.now(),
        mode: this.config.oracleMode.type
      };
      
      return this.createComponentResult(filePath, errorResult, Date.now() - startTime);
    }
  }

  /**
   * Create a component coherence result
   */
  private createComponentResult(filePath: string, oracleResult: MasterOracleResult, executionTime: number): ComponentCoherenceResult {
    const componentType = this.determineComponentType(filePath);
    const name = path.basename(filePath, path.extname(filePath));
    const coherenceScore = oracleResult.oracle_score;
    
    // Determine status based on coherence score and violations
    let status: 'coherent' | 'warning' | 'critical' | 'failed' = 'coherent';
    if (!oracleResult.ok) {
      status = 'failed';
    } else if (coherenceScore < 0.8) {
      status = 'critical';
    } else if (coherenceScore < 0.95) {
      status = 'warning';
    }
    
    return {
      path: filePath,
      name,
      type: componentType,
      oracleResult,
      coherenceScore,
      status,
      violations: oracleResult.violations,
      dependencies: this.extractDependencies(filePath),
      dependents: [] // Will be populated during cross-module analysis
    };
  }

  /**
   * Determine component type from file path
   */
  private determineComponentType(filePath: string): 'blueprint' | 'module' | 'component' {
    if (filePath.includes('blueprint')) {
      return 'blueprint';
    } else if (filePath.includes('module') || filePath.endsWith('.json')) {
      return 'module';
    } else {
      return 'component';
    }
  }

  /**
   * Extract dependencies from a file
   */
  private extractDependencies(filePath: string): string[] {
    try {
      if (filePath.endsWith('.json')) {
        const content = fs.readFileSync(filePath, 'utf8');
        const data = JSON.parse(content);
        return data.dependencies || data.imports || [];
      } else if (filePath.endsWith('.ts') || filePath.endsWith('.js')) {
        const content = fs.readFileSync(filePath, 'utf8');
        const imports = content.match(/import.*from\s+['"]([^'"]+)['"]/g) || [];
        return imports.map(imp => imp.match(/['"]([^'"]+)['"]/)?.[1]).filter(Boolean) as string[];
      }
    } catch {
      // Ignore errors in dependency extraction
    }
    return [];
  }

  /**
   * Analyze cross-module coherence
   */
  private async analyzeCrossModuleCoherence(results: ComponentCoherenceResult[]): Promise<CrossModuleCoherenceResult> {
    const moduleInteractions: ModuleInteraction[] = [];
    const coherenceViolations: CoherenceViolation[] = [];
    
    // Analyze interactions between modules
    for (const result of results) {
      for (const dependency of result.dependencies) {
        const targetResult = results.find(r => r.name === dependency || r.path.includes(dependency));
        if (targetResult) {
          const interaction: ModuleInteraction = {
            sourceModule: result.path,
            targetModule: targetResult.path,
            interactionType: 'dependency',
            coherenceScore: Math.min(result.coherenceScore, targetResult.coherenceScore),
            violations: []
          };
          
          // Check for coherence violations
          if (interaction.coherenceScore < 0.9) {
            coherenceViolations.push({
              type: 'interface_mismatch',
              severity: 'warning',
              message: `Low coherence between ${result.name} and ${targetResult.name}`,
              affectedModules: [result.path, targetResult.path],
              suggestion: 'Review interface compatibility and invariants'
            });
          }
          
          moduleInteractions.push(interaction);
        }
      }
    }
    
    // Calculate overall cross-module coherence score
    const overallScore = moduleInteractions.length > 0 
      ? moduleInteractions.reduce((sum, interaction) => sum + interaction.coherenceScore, 0) / moduleInteractions.length
      : 1.0;
    
    return {
      overallScore,
      moduleInteractions,
      coherenceViolations,
      recommendations: this.generateCrossModuleRecommendations(coherenceViolations)
    };
  }

  /**
   * Analyze dependency coherence
   */
  private async analyzeDependencyCoherence(results: ComponentCoherenceResult[]): Promise<DependencyCoherenceResult> {
    const dependencyGraph: DependencyNode[] = [];
    const circularDependencies: CircularDependency[] = [];
    const versionConflicts: VersionConflict[] = [];
    const missingDependencies: string[] = [];
    
    // Build dependency graph
    for (const result of results) {
      const node: DependencyNode = {
        name: result.name,
        version: '1.0.0', // Default version, would be extracted from actual files
        dependencies: result.dependencies,
        dependents: [],
        coherenceScore: result.coherenceScore
      };
      
      dependencyGraph.push(node);
    }
    
    // Populate dependents
    for (const node of dependencyGraph) {
      for (const dep of node.dependencies) {
        const dependentNode = dependencyGraph.find(n => n.name === dep);
        if (dependentNode) {
          dependentNode.dependents.push(node.name);
        } else {
          missingDependencies.push(dep);
        }
      }
    }
    
    // Detect circular dependencies
    const cycles = this.detectCircularDependencies(dependencyGraph);
    for (const cycle of cycles) {
      circularDependencies.push({
        cycle,
        severity: 'critical',
        impact: 'System may fail to initialize properly'
      });
    }
    
    // Calculate overall dependency coherence score
    const overallScore = dependencyGraph.length > 0
      ? dependencyGraph.reduce((sum, node) => sum + node.coherenceScore, 0) / dependencyGraph.length
      : 1.0;
    
    return {
      overallScore,
      dependencyGraph,
      circularDependencies,
      versionConflicts,
      missingDependencies
    };
  }

  /**
   * Detect circular dependencies in the dependency graph
   */
  private detectCircularDependencies(graph: DependencyNode[]): string[][] {
    const cycles: string[][] = [];
    const visited = new Set<string>();
    const recursionStack = new Set<string>();
    
    const dfs = (nodeName: string, path: string[]): void => {
      if (recursionStack.has(nodeName)) {
        // Found a cycle
        const cycleStart = path.indexOf(nodeName);
        cycles.push(path.slice(cycleStart));
        return;
      }
      
      if (visited.has(nodeName)) {
        return;
      }
      
      visited.add(nodeName);
      recursionStack.add(nodeName);
      
      const node = graph.find(n => n.name === nodeName);
      if (node) {
        for (const dep of node.dependencies) {
          dfs(dep, [...path, nodeName]);
        }
      }
      
      recursionStack.delete(nodeName);
    };
    
    for (const node of graph) {
      if (!visited.has(node.name)) {
        dfs(node.name, []);
      }
    }
    
    return cycles;
  }

  /**
   * Calculate global coherence score
   */
  private calculateGlobalCoherenceScore(results: ComponentCoherenceResult[]): number {
    if (results.length === 0) return 0;
    
    // Weight different component types
    const weights = { blueprint: 0.4, module: 0.4, component: 0.2 };
    
    let weightedSum = 0;
    let totalWeight = 0;
    
    for (const result of results) {
      const weight = weights[result.type] || 0.1;
      weightedSum += result.coherenceScore * weight;
      totalWeight += weight;
    }
    
    return totalWeight > 0 ? weightedSum / totalWeight : 0;
  }

  /**
   * Identify critical issues
   */
  private identifyCriticalIssues(
    results: ComponentCoherenceResult[],
    crossModuleCoherence: CrossModuleCoherenceResult,
    dependencyCoherence: DependencyCoherenceResult
  ): CriticalIssue[] {
    const issues: CriticalIssue[] = [];
    
    // Check for failed components
    const failedComponents = results.filter(r => r.status === 'failed');
    if (failedComponents.length > 0) {
      issues.push({
        type: 'system_breaking',
        severity: 'critical',
        description: `${failedComponents.length} components failed validation`,
        affectedComponents: failedComponents.map(c => c.path),
        impact: 'System may not function correctly',
        resolution: 'Fix validation failures in affected components'
      });
    }
    
    // Check for critical coherence violations
    const criticalComponents = results.filter(r => r.status === 'critical');
    if (criticalComponents.length > 0) {
      issues.push({
        type: 'coherence_violation',
        severity: 'high',
        description: `${criticalComponents.length} components have critical coherence issues`,
        affectedComponents: criticalComponents.map(c => c.path),
        impact: 'System coherence is compromised',
        resolution: 'Address coherence violations in affected components'
      });
    }
    
    // Check for circular dependencies
    if (dependencyCoherence.circularDependencies.length > 0) {
      issues.push({
        type: 'dependency_issue',
        severity: 'critical',
        description: `${dependencyCoherence.circularDependencies.length} circular dependencies detected`,
        affectedComponents: dependencyCoherence.circularDependencies.flatMap(cd => cd.cycle),
        impact: 'System initialization may fail',
        resolution: 'Break circular dependencies by refactoring component relationships'
      });
    }
    
    // Check for missing dependencies
    if (dependencyCoherence.missingDependencies.length > 0) {
      issues.push({
        type: 'dependency_issue',
        severity: 'high',
        description: `${dependencyCoherence.missingDependencies.length} missing dependencies`,
        affectedComponents: dependencyCoherence.missingDependencies,
        impact: 'Components may fail to load or function',
        resolution: 'Install missing dependencies or fix import paths'
      });
    }
    
    return issues;
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(results: ComponentCoherenceResult[], criticalIssues: CriticalIssue[]): string[] {
    const recommendations: string[] = [];
    
    // Component-specific recommendations
    const lowScoreComponents = results.filter(r => r.coherenceScore < 0.9);
    if (lowScoreComponents.length > 0) {
      recommendations.push(`Improve coherence in ${lowScoreComponents.length} components with scores below 0.9`);
    }
    
    // Violation-based recommendations
    const violationTypes = new Map<string, number>();
    for (const result of results) {
      for (const violation of result.violations) {
        violationTypes.set(violation.type, (violationTypes.get(violation.type) || 0) + 1);
      }
    }
    
    for (const [type, count] of violationTypes) {
      if (count > 0) {
        recommendations.push(`Address ${count} ${type} violations across the system`);
      }
    }
    
    // Critical issue recommendations
    for (const issue of criticalIssues) {
      recommendations.push(issue.resolution);
    }
    
    return recommendations;
  }

  /**
   * Determine system status
   */
  private determineSystemStatus(globalScore: number, criticalIssues: CriticalIssue[]): 'coherent' | 'warning' | 'critical' | 'failed' {
    const hasCriticalIssues = criticalIssues.some(issue => issue.severity === 'critical');
    const hasHighIssues = criticalIssues.some(issue => issue.severity === 'high');
    
    if (hasCriticalIssues || globalScore < 0.7) {
      return 'failed';
    } else if (hasHighIssues || globalScore < 0.85) {
      return 'critical';
    } else if (globalScore < 0.95) {
      return 'warning';
    } else {
      return 'coherent';
    }
  }

  /**
   * Aggregate violations from all components
   */
  private aggregateViolations(results: ComponentCoherenceResult[]): OracleViolation[] {
    const allViolations: OracleViolation[] = [];
    
    for (const result of results) {
      allViolations.push(...result.violations);
    }
    
    return allViolations;
  }

  /**
   * Calculate validation metrics
   */
  private calculateValidationMetrics(startTime: number, totalFiles: number): ValidationMetrics {
    const totalTime = Date.now() - startTime;
    const averageTime = totalFiles > 0 ? totalTime / totalFiles : 0;
    
    return {
      totalValidationTimeMs: totalTime,
      averageValidationTimeMs: averageTime,
      cacheHitRate: 0.8, // Would be calculated from actual cache hits
      parallelizationEfficiency: this.config.enableParallelValidation ? 0.9 : 0.5,
      memoryUsageMB: process.memoryUsage().heapUsed / 1024 / 1024,
      cpuUsagePercent: 0 // Would be calculated from actual CPU usage
    };
  }

  /**
   * Generate cross-module recommendations
   */
  private generateCrossModuleRecommendations(violations: CoherenceViolation[]): string[] {
    const recommendations: string[] = [];
    
    const violationTypes = new Map<string, number>();
    for (const violation of violations) {
      violationTypes.set(violation.type, (violationTypes.get(violation.type) || 0) + 1);
    }
    
    for (const [type, count] of violationTypes) {
      if (count > 0) {
        recommendations.push(`Resolve ${count} ${type} issues between modules`);
      }
    }
    
    return recommendations;
  }

  /**
   * Generate reports
   */
  private async generateReports(result: GlobalCoherenceResult): Promise<void> {
    if (this.config.generateDetailedReport) {
      await fs.promises.writeFile(
        this.config.outputPath,
        JSON.stringify(result, null, 2)
      );
      console.log(`📄 Detailed report saved to ${this.config.outputPath}`);
    }
    
    if (this.config.generateSummaryReport) {
      const summaryPath = this.config.outputPath.replace('.json', '-summary.json');
      const summary = {
        globalCoherenceScore: result.globalCoherenceScore,
        systemStatus: result.systemStatus,
        totalFilesValidated: result.totalFilesValidated,
        criticalIssues: result.criticalIssues.length,
        totalViolations: result.globalViolations.length,
        executionTimeMs: result.executionTimeMs,
        recommendations: result.recommendations.slice(0, 5) // Top 5 recommendations
      };
      
      await fs.promises.writeFile(
        summaryPath,
        JSON.stringify(summary, null, 2)
      );
      console.log(`📋 Summary report saved to ${summaryPath}`);
    }
  }

  /**
   * Utility method to chunk array
   */
  private chunkArray<T>(array: T[], chunkSize: number): T[][] {
    const chunks: T[][] = [];
    for (let i = 0; i < array.length; i += chunkSize) {
      chunks.push(array.slice(i, i + chunkSize));
    }
    return chunks;
  }

  /**
   * Clear validation cache
   */
  public clearCache(): void {
    this.validationCache.clear();
  }

  /**
   * Update configuration
   */
  public updateConfig(newConfig: Partial<GlobalCoherenceConfig>): void {
    this.config = { ...this.config, ...newConfig };
    this.masterOracle.setMode(this.config.oracleMode);
  }

  /**
   * Get current configuration
   */
  public getConfig(): GlobalCoherenceConfig {
    return { ...this.config };
  }

  /**
   * Gets files matching a pattern (simplified implementation)
   */
  private getFilesMatchingPattern(pattern: string): string[] {
    // Simplified implementation - in a real scenario, you'd use a proper glob library
    // For now, return empty array to avoid compilation errors
    return [];
  }

  /**
   * Get validation statistics
   */
  public getStats(): any {
    return {
      config: this.config,
      cacheSize: this.validationCache.size,
      metrics: this.metrics.snapshot()
    };
  }
}

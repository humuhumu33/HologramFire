#!/usr/bin/env node

/**
 * Global Coherence Oracle CLI
 * 
 * Command-line interface for running global coherence validation
 * across the entire Hologram system.
 */

import { GlobalCoherenceOracle, GlobalCoherenceConfig } from './GlobalCoherenceOracle';
import { OracleMode } from './MasterHologramOracle';
import fs from 'node:fs';
import path from 'node:path';

interface CLIOptions {
  mode: 'base' | 'enhanced' | 'ml-enhanced' | 'strict' | 'development' | 'middleware';
  output: string;
  config: string;
  verbose: boolean;
  parallel: boolean;
  maxConcurrent: number;
  threshold: number;
  blueprintOnly: boolean;
  moduleOnly: boolean;
  componentOnly: boolean;
  noCache: boolean;
  help: boolean;
}

class GlobalCoherenceCLI {
  private options: CLIOptions;

  constructor() {
    this.options = this.parseArguments();
  }

  /**
   * Parse command line arguments
   */
  private parseArguments(): CLIOptions {
    const args = process.argv.slice(2);
    const options: CLIOptions = {
      mode: 'strict',
      output: 'global-coherence-report.json',
      config: '',
      verbose: false,
      parallel: true,
      maxConcurrent: 10,
      threshold: 0.95,
      blueprintOnly: false,
      moduleOnly: false,
      componentOnly: false,
      noCache: false,
      help: false
    };

    for (let i = 0; i < args.length; i++) {
      const arg = args[i];
      
      switch (arg) {
        case '--mode':
        case '-m':
          options.mode = args[++i] as any || 'strict';
          break;
        case '--output':
        case '-o':
          options.output = args[++i] || 'global-coherence-report.json';
          break;
        case '--config':
        case '-c':
          options.config = args[++i] || '';
          break;
        case '--verbose':
        case '-v':
          options.verbose = true;
          break;
        case '--no-parallel':
          options.parallel = false;
          break;
        case '--max-concurrent':
          options.maxConcurrent = parseInt(args[++i]) || 10;
          break;
        case '--threshold':
        case '-t':
          options.threshold = parseFloat(args[++i]) || 0.95;
          break;
        case '--blueprint-only':
          options.blueprintOnly = true;
          break;
        case '--module-only':
          options.moduleOnly = true;
          break;
        case '--component-only':
          options.componentOnly = true;
          break;
        case '--no-cache':
          options.noCache = true;
          break;
        case '--help':
        case '-h':
          options.help = true;
          break;
        default:
          if (arg.startsWith('-')) {
            console.warn(`Unknown option: ${arg}`);
          }
          break;
      }
    }

    return options;
  }

  /**
   * Show help information
   */
  private showHelp(): void {
    console.log(`
🔍 Global Coherence Oracle CLI

Usage: npx ts-node global-coherence-cli.ts [options]

Options:
  -m, --mode <mode>           Oracle mode (base|enhanced|ml-enhanced|strict|development|middleware) [default: strict]
  -o, --output <file>         Output file path [default: global-coherence-report.json]
  -c, --config <file>         Configuration file path
  -v, --verbose               Enable verbose output
  --no-parallel               Disable parallel validation
  --max-concurrent <num>      Maximum concurrent validations [default: 10]
  -t, --threshold <score>     Coherence threshold [default: 0.95]
  --blueprint-only            Validate only blueprint files
  --module-only               Validate only module files
  --component-only            Validate only component files
  --no-cache                  Disable validation caching
  -h, --help                  Show this help message

Examples:
  # Run with default settings
  npx ts-node global-coherence-cli.ts

  # Run with custom configuration
  npx ts-node global-coherence-cli.ts --config config.json --output my-report.json

  # Run in ML-enhanced mode with verbose output
  npx ts-node global-coherence-cli.ts --mode ml-enhanced --verbose

  # Validate only blueprints with custom threshold
  npx ts-node global-coherence-cli.ts --blueprint-only --threshold 0.98

  # Run without parallel processing
  npx ts-node global-coherence-cli.ts --no-parallel --max-concurrent 1
`);
  }

  /**
   * Load configuration from file
   */
  private loadConfig(configPath: string): Partial<GlobalCoherenceConfig> {
    try {
      if (fs.existsSync(configPath)) {
        const configData = fs.readFileSync(configPath, 'utf8');
        return JSON.parse(configData);
      }
    } catch (error) {
      console.warn(`Warning: Could not load config file ${configPath}: ${error}`);
    }
    return {};
  }

  /**
   * Create configuration from CLI options
   */
  private createConfig(): GlobalCoherenceConfig {
    const oracleMode: OracleMode = {
      type: this.options.mode,
      config: {
        threshold: this.options.threshold,
        enableRealTimeMonitoring: this.options.mode === 'strict',
        enableMLOptimization: this.options.mode === 'ml-enhanced',
        enableAdaptiveScoring: this.options.mode !== 'base'
      }
    };

    const config: GlobalCoherenceConfig = {
      enableBlueprintValidation: !this.options.moduleOnly && !this.options.componentOnly,
      enableModuleValidation: !this.options.blueprintOnly && !this.options.componentOnly,
      enableComponentValidation: !this.options.blueprintOnly && !this.options.moduleOnly,
      enableCrossModuleValidation: true,
      enableDependencyValidation: true,
      oracleMode,
      blueprintPaths: ['atlas-12288/blueprint/**/*.json'],
      modulePaths: ['modules/**/*.json', 'data/modules/**/*.json'],
      componentPaths: ['src/**/*.ts', 'src/**/*.js'],
      excludePaths: ['node_modules/**', 'build/**', 'dist/**', 'tests/**'],
      globalCoherenceThreshold: this.options.threshold,
      moduleCoherenceThreshold: this.options.threshold - 0.05,
      blueprintCoherenceThreshold: this.options.threshold,
      enableParallelValidation: this.options.parallel,
      maxConcurrentValidations: this.options.maxConcurrent,
      enableCaching: !this.options.noCache,
      cacheTimeoutMs: 30000,
      generateDetailedReport: true,
      generateSummaryReport: true,
      outputPath: this.options.output
    };

    // Load additional config from file if specified
    if (this.options.config) {
      const fileConfig = this.loadConfig(this.options.config);
      return { ...config, ...fileConfig };
    }

    return config;
  }

  /**
   * Run the global coherence validation
   */
  async run(): Promise<void> {
    if (this.options.help) {
      this.showHelp();
      return;
    }

    try {
      console.log('🚀 Starting Global Coherence Oracle...\n');
      
      // Create configuration
      const config = this.createConfig();
      
      if (this.options.verbose) {
        console.log('📋 Configuration:');
        console.log(`  Mode: ${config.oracleMode.type}`);
        console.log(`  Threshold: ${config.globalCoherenceThreshold}`);
        console.log(`  Parallel: ${config.enableParallelValidation}`);
        console.log(`  Max Concurrent: ${config.maxConcurrentValidations}`);
        console.log(`  Output: ${config.outputPath}`);
        console.log(`  Blueprint Validation: ${config.enableBlueprintValidation}`);
        console.log(`  Module Validation: ${config.enableModuleValidation}`);
        console.log(`  Component Validation: ${config.enableComponentValidation}`);
        console.log('');
      }

      // Create and run oracle
      const oracle = new GlobalCoherenceOracle(config);
      const result = await oracle.validateGlobalCoherence();

      // Display results
      this.displayResults(result);

      // Exit with appropriate code
      const exitCode = this.determineExitCode(result);
      process.exit(exitCode);

    } catch (error) {
      console.error('❌ Global coherence validation failed:');
      console.error(error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  }

  /**
   * Display validation results
   */
  private displayResults(result: any): void {
    console.log('\n📊 Global Coherence Validation Results');
    console.log('=====================================');
    
    // Overall status
    const statusEmoji: Record<string, string> = {
      coherent: '✅',
      warning: '⚠️',
      critical: '🚨',
      failed: '❌'
    };
    
    console.log(`\n${statusEmoji[result.systemStatus] || '❓'} System Status: ${result.systemStatus.toUpperCase()}`);
    console.log(`📈 Global Coherence Score: ${(result.globalCoherenceScore * 100).toFixed(1)}%`);
    console.log(`⏱️  Execution Time: ${result.executionTimeMs}ms`);
    console.log(`📁 Files Validated: ${result.totalFilesValidated}`);
    
    // Component breakdown
    console.log('\n📋 Component Breakdown:');
    console.log(`  Blueprints: ${result.blueprintResults.length} (${this.getStatusCount(result.blueprintResults)})`);
    console.log(`  Modules: ${result.moduleResults.length} (${this.getStatusCount(result.moduleResults)})`);
    console.log(`  Components: ${result.componentResults.length} (${this.getStatusCount(result.componentResults)})`);
    
    // Critical issues
    if (result.criticalIssues.length > 0) {
      console.log('\n🚨 Critical Issues:');
      result.criticalIssues.forEach((issue: any, index: number) => {
        console.log(`  ${index + 1}. ${issue.description}`);
        console.log(`     Severity: ${issue.severity}`);
        console.log(`     Impact: ${issue.impact}`);
        console.log(`     Resolution: ${issue.resolution}`);
        if (this.options.verbose && issue.affectedComponents.length > 0) {
          console.log(`     Affected: ${issue.affectedComponents.slice(0, 3).join(', ')}${issue.affectedComponents.length > 3 ? '...' : ''}`);
        }
        console.log('');
      });
    }
    
    // Cross-module coherence
    if (result.crossModuleCoherence) {
      console.log(`\n🔗 Cross-Module Coherence: ${(result.crossModuleCoherence.overallScore * 100).toFixed(1)}%`);
      if (result.crossModuleCoherence.coherenceViolations.length > 0) {
        console.log(`  Violations: ${result.crossModuleCoherence.coherenceViolations.length}`);
      }
    }
    
    // Dependency coherence
    if (result.dependencyCoherence) {
      console.log(`\n📦 Dependency Coherence: ${(result.dependencyCoherence.overallScore * 100).toFixed(1)}%`);
      if (result.dependencyCoherence.circularDependencies.length > 0) {
        console.log(`  Circular Dependencies: ${result.dependencyCoherence.circularDependencies.length}`);
      }
      if (result.dependencyCoherence.missingDependencies.length > 0) {
        console.log(`  Missing Dependencies: ${result.dependencyCoherence.missingDependencies.length}`);
      }
    }
    
    // Top recommendations
    if (result.recommendations.length > 0) {
      console.log('\n💡 Top Recommendations:');
      result.recommendations.slice(0, 5).forEach((rec: string, index: number) => {
        console.log(`  ${index + 1}. ${rec}`);
      });
    }
    
    // Performance metrics
    if (this.options.verbose && result.validationMetrics) {
      console.log('\n⚡ Performance Metrics:');
      console.log(`  Total Time: ${result.validationMetrics.totalValidationTimeMs}ms`);
      console.log(`  Average Time: ${result.validationMetrics.averageValidationTimeMs.toFixed(1)}ms`);
      console.log(`  Cache Hit Rate: ${(result.validationMetrics.cacheHitRate * 100).toFixed(1)}%`);
      console.log(`  Memory Usage: ${result.validationMetrics.memoryUsageMB.toFixed(1)}MB`);
    }
    
    console.log('\n📄 Reports generated:');
    console.log(`  Detailed: ${result.validationMetrics ? 'global-coherence-report.json' : 'N/A'}`);
    console.log(`  Summary: ${result.validationMetrics ? 'global-coherence-report-summary.json' : 'N/A'}`);
  }

  /**
   * Get status count string for components
   */
  private getStatusCount(components: any[]): string {
    const counts: Record<string, number> = {
      coherent: 0,
      warning: 0,
      critical: 0,
      failed: 0
    };
    
    components.forEach(comp => {
      if (comp.status in counts) {
        counts[comp.status]++;
      }
    });
    
    const parts = [];
    if (counts.coherent > 0) parts.push(`${counts.coherent}✅`);
    if (counts.warning > 0) parts.push(`${counts.warning}⚠️`);
    if (counts.critical > 0) parts.push(`${counts.critical}🚨`);
    if (counts.failed > 0) parts.push(`${counts.failed}❌`);
    
    return parts.join(' ');
  }

  /**
   * Determine exit code based on results
   */
  private determineExitCode(result: any): number {
    switch (result.systemStatus) {
      case 'coherent':
        return 0;
      case 'warning':
        return 1;
      case 'critical':
        return 2;
      case 'failed':
        return 3;
      default:
        return 1;
    }
  }
}

// Run CLI if this file is executed directly
if (require.main === module) {
  const cli = new GlobalCoherenceCLI();
  cli.run().catch(error => {
    console.error('Fatal error:', error);
    process.exit(1);
  });
}

export { GlobalCoherenceCLI };

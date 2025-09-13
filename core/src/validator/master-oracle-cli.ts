#!/usr/bin/env node

import { MasterHologramOracle, OracleMode, MasterOracleConfig } from "./MasterHologramOracle";
import { Metrics } from "../monitoring/metrics/Metrics";
import fs from "node:fs";
import path from "node:path";

/**
 * Master Oracle CLI - Unified command-line interface for all oracle operations
 * 
 * This CLI consolidates all oracle functionality into a single tool with mode selection.
 * It replaces the multiple separate CLI tools with a unified interface.
 */

interface CLIOptions {
  mode: 'base' | 'enhanced' | 'ml-enhanced' | 'strict' | 'development' | 'middleware';
  input: string;
  output?: string;
  config?: string;
  threshold?: number;
  verbose?: boolean;
  watch?: boolean;
  help?: boolean;
}

class MasterOracleCLI {
  private oracle: MasterHologramOracle;
  private metrics: Metrics;
  private options: CLIOptions;

  constructor() {
    this.metrics = new Metrics();
    this.options = this.parseArguments();
    this.oracle = this.initializeOracle();
  }

  private parseArguments(): CLIOptions {
    const args = process.argv.slice(2);
    const options: CLIOptions = {
      mode: 'enhanced',
      input: '',
      verbose: false,
      watch: false,
      help: false
    };

    for (let i = 0; i < args.length; i++) {
      const arg = args[i];
      
      switch (arg) {
        case '--mode':
        case '-m':
          options.mode = args[++i] as any;
          break;
        case '--input':
        case '-i':
          options.input = args[++i];
          break;
        case '--output':
        case '-o':
          options.output = args[++i];
          break;
        case '--config':
        case '-c':
          options.config = args[++i];
          break;
        case '--threshold':
        case '-t':
          options.threshold = parseFloat(args[++i]);
          break;
        case '--verbose':
        case '-v':
          options.verbose = true;
          break;
        case '--watch':
        case '-w':
          options.watch = true;
          break;
        case '--help':
        case '-h':
          options.help = true;
          break;
        default:
          // Handle positional arguments
          if (!options.input && !arg.startsWith('-')) {
            options.input = arg;
          }
          // Handle mode as first positional argument
          else if (!options.input && ['base', 'enhanced', 'ml-enhanced', 'strict', 'development', 'middleware'].includes(arg)) {
            options.mode = arg as any;
          }
          break;
      }
    }

    return options;
  }

  private initializeOracle(): MasterHologramOracle {
    const config: Partial<MasterOracleConfig> = {};

    // Load config from file if specified
    if (this.options.config) {
      try {
        const configData = JSON.parse(fs.readFileSync(this.options.config, 'utf8'));
        Object.assign(config, configData);
      } catch (error) {
        console.error(`Error loading config file: ${error}`);
        process.exit(1);
      }
    }

    // Apply CLI overrides
    if (this.options.threshold !== undefined) {
      config.threshold = this.options.threshold;
    }

    // Set mode-specific defaults
    switch (this.options.mode) {
      case 'base':
        config.enableAdaptiveScoring = false;
        config.enablePerformanceCalibration = false;
        config.enableMLOptimization = false;
        config.enableRealTimeMonitoring = false;
        break;
      case 'enhanced':
        config.enableAdaptiveScoring = true;
        config.enablePerformanceCalibration = true;
        config.enableInvariantVerification = true;
        break;
      case 'ml-enhanced':
        config.enableAdaptiveScoring = true;
        config.enablePerformanceCalibration = true;
        config.enableInvariantVerification = true;
        config.enableMLOptimization = true;
        config.enableMLPerformancePrediction = true;
        config.enableMLAnomalyDetection = true;
        config.enableMLPatternRecognition = true;
        break;
      case 'strict':
        config.enableAdaptiveScoring = true;
        config.enablePerformanceCalibration = true;
        config.enableInvariantVerification = true;
        config.enableRealTimeMonitoring = true;
        config.enableTrendAnalysis = true;
        break;
      case 'development':
        config.enableAdaptiveScoring = true;
        config.enableInvariantVerification = true;
        config.enableRealTimeFeedback = true;
        config.enableValidationCache = true;
        break;
      case 'middleware':
        config.enableAdaptiveScoring = true;
        config.enableInvariantVerification = true;
        config.enableValidationCache = true;
        break;
    }

    const mode: OracleMode = {
      type: this.options.mode,
      config
    };

    return new MasterHologramOracle(mode);
  }

  public async run(): Promise<void> {
    if (this.options.help) {
      this.showHelp();
      return;
    }

    if (!this.options.input) {
      console.error('Error: Input file or directory is required');
      this.showHelp();
      process.exit(1);
    }

    try {
      if (this.options.watch) {
        await this.runWatchMode();
      } else {
        await this.runSingleValidation();
      }
    } catch (error) {
      console.error(`Error: ${error instanceof Error ? error.message : String(error)}`);
      process.exit(1);
    }
  }

  private async runSingleValidation(): Promise<void> {
    const startTime = Date.now();
    
    if (this.options.verbose) {
      console.log(`Running ${this.options.mode} oracle validation on: ${this.options.input}`);
    }

    const result = await this.oracle.validate(this.options.input);
    
    const executionTime = Date.now() - startTime;
    
    if (this.options.verbose) {
      this.printVerboseResult(result, executionTime);
    } else {
      this.printSimpleResult(result);
    }

    if (this.options.output) {
      this.saveResult(result);
    }

    // Exit with appropriate code
    process.exit(result.ok ? 0 : 1);
  }

  private async runWatchMode(): Promise<void> {
    console.log(`Watching ${this.options.input} for changes...`);
    
    if (!fs.existsSync(this.options.input)) {
      console.error(`Error: Input path does not exist: ${this.options.input}`);
      process.exit(1);
    }

    const watchPath = fs.statSync(this.options.input).isDirectory() 
      ? this.options.input 
      : path.dirname(this.options.input);

    fs.watch(watchPath, { recursive: true }, async (eventType, filename) => {
      if (filename && (filename.endsWith('.json') || filename.endsWith('.ts') || filename.endsWith('.js'))) {
        const fullPath = path.join(watchPath, filename);
        
        if (fs.existsSync(fullPath)) {
          console.log(`\n[${new Date().toISOString()}] File changed: ${filename}`);
          
          try {
            const result = await this.oracle.validate(fullPath);
            this.printSimpleResult(result);
          } catch (error) {
            console.error(`Validation error: ${error}`);
          }
        }
      }
    });

    // Keep the process running
    process.on('SIGINT', () => {
      console.log('\nStopping watch mode...');
      this.oracle.destroy();
      process.exit(0);
    });
  }

  private printSimpleResult(result: any): void {
    const status = result.ok ? '✅ PASS' : '❌ FAIL';
    const score = (result.oracle_score * 100).toFixed(1);
    const violations = result.violations.length;
    
    console.log(`${status} | Score: ${score}% | Violations: ${violations}`);
    
    if (!result.ok && result.violations.length > 0) {
      console.log('\nViolations:');
      result.violations.forEach((violation: any, index: number) => {
        console.log(`  ${index + 1}. [${violation.severity.toUpperCase()}] ${violation.type}: ${violation.message}`);
      });
    }

    // Mode-specific output
    switch (this.options.mode) {
      case 'ml-enhanced':
        if (result.mlRecommendations && result.mlRecommendations.length > 0) {
          console.log('\nML Recommendations:');
          result.mlRecommendations.forEach((rec: string, index: number) => {
            console.log(`  ${index + 1}. ${rec}`);
          });
        }
        break;
      case 'development':
        if (result.suggestions && result.suggestions.length > 0) {
          console.log('\nSuggestions:');
          result.suggestions.forEach((suggestion: string, index: number) => {
            console.log(`  ${index + 1}. ${suggestion}`);
          });
        }
        break;
      case 'strict':
        if (result.coherenceScore !== undefined) {
          console.log(`Coherence Score: ${(result.coherenceScore * 100).toFixed(1)}%`);
        }
        break;
    }
  }

  private printVerboseResult(result: any, executionTime: number): void {
    console.log('\n' + '='.repeat(60));
    console.log(`ORACLE VALIDATION RESULT (${this.options.mode.toUpperCase()} MODE)`);
    console.log('='.repeat(60));
    
    console.log(`Status: ${result.ok ? 'PASS' : 'FAIL'}`);
    console.log(`Oracle Score: ${(result.oracle_score * 100).toFixed(2)}%`);
    console.log(`Execution Time: ${executionTime}ms`);
    console.log(`Timestamp: ${new Date(result.timestamp).toISOString()}`);
    console.log(`Holographic Fingerprint: ${result.holographic_fingerprint}`);
    
    if (result.violations.length > 0) {
      console.log(`\nViolations (${result.violations.length}):`);
      result.violations.forEach((violation: any, index: number) => {
        console.log(`  ${index + 1}. [${violation.severity.toUpperCase()}] ${violation.type}`);
        console.log(`     Message: ${violation.message}`);
        if (violation.location) {
          console.log(`     Location: ${violation.location}`);
        }
        if (violation.suggestion) {
          console.log(`     Suggestion: ${violation.suggestion}`);
        }
      });
    }

    // Mode-specific verbose output
    switch (this.options.mode) {
      case 'enhanced':
        if (result.adaptiveScoring) {
          console.log(`\nAdaptive Scoring: ${(result.adaptiveScoring.overallScore * 100).toFixed(2)}%`);
          console.log(`Components: ${result.adaptiveScoring.components.length}`);
        }
        if (result.invariantVerifications) {
          console.log(`Invariant Verifications: ${result.invariantVerifications.length}`);
        }
        break;
        
      case 'ml-enhanced':
        if (result.mlConfidence !== undefined) {
          console.log(`ML Confidence: ${(result.mlConfidence * 100).toFixed(2)}%`);
        }
        if (result.mlRecommendations && result.mlRecommendations.length > 0) {
          console.log(`\nML Recommendations (${result.mlRecommendations.length}):`);
          result.mlRecommendations.forEach((rec: string, index: number) => {
            console.log(`  ${index + 1}. ${rec}`);
          });
        }
        break;
        
      case 'strict':
        if (result.coherenceScore !== undefined) {
          console.log(`Coherence Score: ${(result.coherenceScore * 100).toFixed(2)}%`);
        }
        if (result.realTimeMetrics) {
          console.log(`\nReal-time Metrics:`);
          console.log(`  Coherence Level: ${(result.realTimeMetrics.coherenceLevel * 100).toFixed(2)}%`);
          console.log(`  Stability Index: ${(result.realTimeMetrics.stabilityIndex * 100).toFixed(2)}%`);
          console.log(`  Energy Efficiency: ${(result.realTimeMetrics.energyEfficiency * 100).toFixed(2)}%`);
        }
        break;
        
      case 'development':
        if (result.suggestions && result.suggestions.length > 0) {
          console.log(`\nSuggestions (${result.suggestions.length}):`);
          result.suggestions.forEach((suggestion: string, index: number) => {
            console.log(`  ${index + 1}. ${suggestion}`);
          });
        }
        if (result.quickFixes && result.quickFixes.length > 0) {
          console.log(`\nQuick Fixes (${result.quickFixes.length}):`);
          result.quickFixes.forEach((fix: string, index: number) => {
            console.log(`  ${index + 1}. ${fix}`);
          });
        }
        break;
    }
    
    console.log('\n' + '='.repeat(60));
  }

  private saveResult(result: any): void {
    try {
      const outputData = {
        timestamp: new Date().toISOString(),
        mode: this.options.mode,
        input: this.options.input,
        result
      };
      
      fs.writeFileSync(this.options.output!, JSON.stringify(outputData, null, 2));
      console.log(`\nResult saved to: ${this.options.output}`);
    } catch (error) {
      console.error(`Error saving result: ${error}`);
    }
  }

  private showHelp(): void {
    console.log(`
Master Hologram Oracle CLI - Unified Oracle Validation Tool

USAGE:
  master-oracle-cli [OPTIONS] <input>

MODES:
  base          Basic holographic validation only
  enhanced      Enhanced validation with adaptive scoring and performance calibration
  ml-enhanced   ML-enhanced validation with optimization and prediction
  strict        Strict validation with real-time monitoring and coherence checking
  development   Development-focused validation with real-time feedback
  middleware    Middleware validation for new code additions

OPTIONS:
  -m, --mode <mode>           Oracle mode (default: enhanced)
  -i, --input <path>          Input file or directory
  -o, --output <file>         Output file for results
  -c, --config <file>         Configuration file
  -t, --threshold <number>    Oracle threshold (0-1, default: 0.95)
  -v, --verbose               Verbose output
  -w, --watch                 Watch mode for continuous validation
  -h, --help                  Show this help

EXAMPLES:
  # Basic validation
  master-oracle-cli --mode base modules/example.json

  # Enhanced validation with verbose output
  master-oracle-cli --mode enhanced --verbose modules/example.json

  # ML-enhanced validation with custom threshold
  master-oracle-cli --mode ml-enhanced --threshold 0.9 modules/example.json

  # Strict validation with output file
  master-oracle-cli --mode strict --output result.json modules/example.json

  # Development mode with watch
  master-oracle-cli --mode development --watch src/

  # Middleware validation
  master-oracle-cli --mode middleware --config config.json new-code.ts

CONFIGURATION:
  Configuration files should be JSON format with oracle settings:
  {
    "threshold": 0.95,
    "enableAdaptiveScoring": true,
    "enableMLOptimization": false,
    "enableRealTimeMonitoring": false
  }

EXIT CODES:
  0  Validation passed
  1  Validation failed or error occurred
`);
  }
}

// Run the CLI if this file is executed directly
if (require.main === module) {
  const cli = new MasterOracleCLI();
  cli.run().catch(error => {
    console.error(`Fatal error: ${error}`);
    process.exit(1);
  });
}

export { MasterOracleCLI };

#!/usr/bin/env node

/**
 * Proof Chain CLI Tool
 * 
 * Command-line interface for proof chain operations, monitoring, and compliance checking.
 * Provides easy-to-use commands for developers and operators.
 */

import { ProofChainAPI, createProofChainAPI } from "../ProofChainAPI";
import { readFileSync, writeFileSync, existsSync } from "fs";
import { join } from "path";

interface CLIConfig {
  configFile?: string;
  outputFormat: "json" | "table" | "yaml";
  verbose: boolean;
  quiet: boolean;
}

class ProofChainCLI {
  private api: ProofChainAPI;
  private config: CLIConfig;

  constructor(config: CLIConfig) {
    this.config = config;
    this.api = createProofChainAPI({
      enableMonitoring: true,
      enableCompliance: true,
      enableProvenance: true,
      autoStartMonitoring: true
    });
  }

  /**
   * Execute a data transformation with proof
   */
  async executeTransform(args: {
    operation: string;
    input: string;
    transformFn: string;
    options?: string;
  }): Promise<void> {
    try {
      const input = JSON.parse(args.input);
      const transformFn = new Function("input", `return ${args.transformFn}`) as (input: any) => unknown;

      const result = await this.api.transformData(
        args.operation,
        input,
        transformFn,
        args.options ? JSON.parse(args.options) : {}
      );

      this.outputResult("Transform Result", result);
    } catch (error) {
      this.outputError("Transform failed", error);
    }
  }

  /**
   * Execute a computation with proof
   */
  async executeCompute(args: {
    operation: string;
    input: string;
    computeFn: string;
    options?: string;
  }): Promise<void> {
    try {
      const input = JSON.parse(args.input);
      const computeFn = new Function("input", `return ${args.computeFn}`) as (input: any) => unknown;

      const result = await this.api.compute(
        args.operation,
        input,
        computeFn,
        args.options ? JSON.parse(args.options) : {}
      );

      this.outputResult("Compute Result", result);
    } catch (error) {
      this.outputError("Compute failed", error);
    }
  }

  /**
   * Verify a proof chain
   */
  async verifyChain(args: { chainId: string }): Promise<void> {
    try {
      const result = await this.api.verifyChain(args.chainId);
      this.outputResult("Chain Verification", result);
    } catch (error) {
      this.outputError("Chain verification failed", error);
    }
  }

  /**
   * Trace provenance
   */
  async traceProvenance(args: { startNodeId: string; endNodeId?: string }): Promise<void> {
    try {
      const result = await this.api.traceProvenance(args.startNodeId, args.endNodeId);
      this.outputResult("Provenance Trace", result);
    } catch (error) {
      this.outputError("Provenance trace failed", error);
    }
  }

  /**
   * Generate compliance report
   */
  async generateComplianceReport(): Promise<void> {
    try {
      const report = await this.api.generateComplianceReport();
      this.outputResult("Compliance Report", report);
    } catch (error) {
      this.outputError("Compliance report generation failed", error);
    }
  }

  /**
   * Get alerts
   */
  async getAlerts(args: { unresolved?: boolean }): Promise<void> {
    try {
      const alerts = args.unresolved 
        ? this.api.getUnresolvedAlerts()
        : this.api.getAlerts();
      
      this.outputResult("Alerts", alerts);
    } catch (error) {
      this.outputError("Failed to get alerts", error);
    }
  }

  /**
   * Resolve an alert
   */
  async resolveAlert(args: { alertId: string }): Promise<void> {
    try {
      this.api.resolveAlert(args.alertId);
      console.log(`Alert ${args.alertId} resolved successfully`);
    } catch (error) {
      this.outputError("Failed to resolve alert", error);
    }
  }

  /**
   * Get system metrics
   */
  async getMetrics(): Promise<void> {
    try {
      const metrics = this.api.getMetrics();
      this.outputResult("System Metrics", metrics);
    } catch (error) {
      this.outputError("Failed to get metrics", error);
    }
  }

  /**
   * Get chain statistics
   */
  async getChainStatistics(): Promise<void> {
    try {
      const statistics = this.api.getChainStatistics();
      this.outputResult("Chain Statistics", statistics);
    } catch (error) {
      this.outputError("Failed to get chain statistics", error);
    }
  }

  /**
   * Start monitoring
   */
  async startMonitoring(): Promise<void> {
    try {
      this.api.startMonitoring();
      console.log("Monitoring started successfully");
    } catch (error) {
      this.outputError("Failed to start monitoring", error);
    }
  }

  /**
   * Stop monitoring
   */
  async stopMonitoring(): Promise<void> {
    try {
      this.api.stopMonitoring();
      console.log("Monitoring stopped successfully");
    } catch (error) {
      this.outputError("Failed to stop monitoring", error);
    }
  }

  /**
   * Execute a script file
   */
  async executeScript(args: { scriptFile: string }): Promise<void> {
    try {
      if (!existsSync(args.scriptFile)) {
        throw new Error(`Script file not found: ${args.scriptFile}`);
      }

      const script = readFileSync(args.scriptFile, "utf8");
      const commands = JSON.parse(script);

      for (const command of commands) {
        await this.executeCommand(command);
      }

      console.log("Script executed successfully");
    } catch (error) {
      this.outputError("Script execution failed", error);
    }
  }

  /**
   * Execute a single command
   */
  private async executeCommand(command: any): Promise<void> {
    const { action, args } = command;

    switch (action) {
      case "transform":
        await this.executeTransform(args);
        break;
      case "compute":
        await this.executeCompute(args);
        break;
      case "verify":
        await this.verifyChain(args);
        break;
      case "trace":
        await this.traceProvenance(args);
        break;
      case "compliance":
        await this.generateComplianceReport();
        break;
      case "alerts":
        await this.getAlerts(args);
        break;
      case "resolve":
        await this.resolveAlert(args);
        break;
      case "metrics":
        await this.getMetrics();
        break;
      case "statistics":
        await this.getChainStatistics();
        break;
      case "start_monitoring":
        await this.startMonitoring();
        break;
      case "stop_monitoring":
        await this.stopMonitoring();
        break;
      default:
        throw new Error(`Unknown command: ${action}`);
    }
  }

  /**
   * Output result in the specified format
   */
  private outputResult(title: string, data: any): void {
    if (this.config.quiet) return;

    console.log(`\n=== ${title} ===`);
    
    switch (this.config.outputFormat) {
      case "json":
        console.log(JSON.stringify(data, null, 2));
        break;
      case "yaml":
        console.log(this.toYaml(data));
        break;
      case "table":
        console.log(this.toTable(data));
        break;
      default:
        console.log(JSON.stringify(data, null, 2));
    }
  }

  /**
   * Output error
   */
  private outputError(message: string, error: any): void {
    if (this.config.quiet) return;

    console.error(`\n❌ ${message}:`);
    console.error(error instanceof Error ? error.message : String(error));
    
    if (this.config.verbose && error instanceof Error) {
      console.error(error.stack);
    }
  }

  /**
   * Convert data to YAML format (simplified)
   */
  private toYaml(data: any): string {
    // This is a simplified YAML converter
    // In a real implementation, you'd use a proper YAML library
    return JSON.stringify(data, null, 2).replace(/"/g, "").replace(/:/g, ": ");
  }

  /**
   * Convert data to table format (simplified)
   */
  private toTable(data: any): string {
    if (Array.isArray(data)) {
      if (data.length === 0) return "No data";
      
      const headers = Object.keys(data[0]);
      const table = [headers.join(" | ")];
      table.push(headers.map(() => "---").join(" | "));
      
      for (const row of data) {
        const values = headers.map(header => String(row[header] || ""));
        table.push(values.join(" | "));
      }
      
      return table.join("\n");
    } else {
      return JSON.stringify(data, null, 2);
    }
  }

  /**
   * Shutdown the CLI
   */
  shutdown(): void {
    this.api.shutdown();
  }
}

// CLI argument parsing and execution
function parseArgs(): { command: string; args: any; config: CLIConfig } {
  const args = process.argv.slice(2);
  
  if (args.length === 0) {
    showHelp();
    process.exit(0);
  }

  const command = args[0];
  const config: CLIConfig = {
    outputFormat: "json",
    verbose: false,
    quiet: false
  };

  const commandArgs: any = {};

  // Parse arguments
  for (let i = 1; i < args.length; i++) {
    const arg = args[i];
    
    if (arg.startsWith("--")) {
      const key = arg.slice(2);
      const value = args[i + 1];
      
      switch (key) {
        case "format":
          config.outputFormat = value as "json" | "table" | "yaml";
          i++;
          break;
        case "config":
          config.configFile = value;
          i++;
          break;
        case "verbose":
          config.verbose = true;
          break;
        case "quiet":
          config.quiet = true;
          break;
        default:
          commandArgs[key] = value;
          i++;
      }
    } else if (arg.startsWith("-")) {
      switch (arg) {
        case "-v":
          config.verbose = true;
          break;
        case "-q":
          config.quiet = true;
          break;
        case "-f":
          config.outputFormat = args[i + 1] as "json" | "table" | "yaml";
          i++;
          break;
        default:
          commandArgs[arg.slice(1)] = args[i + 1];
          i++;
      }
    } else {
      // Positional argument
      if (!commandArgs.input) {
        commandArgs.input = arg;
      } else if (!commandArgs.output) {
        commandArgs.output = arg;
      }
    }
  }

  return { command, args: commandArgs, config };
}

function showHelp(): void {
  console.log(`
Proof Chain CLI Tool

Usage: proof-chain <command> [options]

Commands:
  transform <operation> <input> <transformFn> [options]  Execute data transformation with proof
  compute <operation> <input> <computeFn> [options]     Execute computation with proof
  verify <chainId>                                      Verify a proof chain
  trace <startNodeId> [endNodeId]                       Trace provenance
  compliance                                            Generate compliance report
  alerts [--unresolved]                                 Get alerts
  resolve <alertId>                                     Resolve an alert
  metrics                                               Get system metrics
  statistics                                            Get chain statistics
  start-monitoring                                      Start monitoring
  stop-monitoring                                       Stop monitoring
  script <scriptFile>                                   Execute script file

Options:
  --format <format>     Output format (json, table, yaml) [default: json]
  --config <file>       Configuration file
  --verbose, -v         Verbose output
  --quiet, -q           Quiet mode
  --help, -h            Show this help

Examples:
  proof-chain transform "double" "[1,2,3]" "input.map(x => x * 2)"
  proof-chain compute "square" "5" "input * input"
  proof-chain verify "chain-123"
  proof-chain trace "node-456" "node-789"
  proof-chain compliance
  proof-chain alerts --unresolved
  proof-chain metrics
`);
}

// Main execution
async function main() {
  const { command, args, config } = parseArgs();
  const cli = new ProofChainCLI(config);

  try {
    switch (command) {
      case "transform":
        await cli.executeTransform(args);
        break;
      case "compute":
        await cli.executeCompute(args);
        break;
      case "verify":
        await cli.verifyChain(args);
        break;
      case "trace":
        await cli.traceProvenance(args);
        break;
      case "compliance":
        await cli.generateComplianceReport();
        break;
      case "alerts":
        await cli.getAlerts(args);
        break;
      case "resolve":
        await cli.resolveAlert(args);
        break;
      case "metrics":
        await cli.getMetrics();
        break;
      case "statistics":
        await cli.getChainStatistics();
        break;
      case "start-monitoring":
        await cli.startMonitoring();
        break;
      case "stop-monitoring":
        await cli.stopMonitoring();
        break;
      case "script":
        await cli.executeScript(args);
        break;
      case "help":
      case "--help":
      case "-h":
        showHelp();
        break;
      default:
        console.error(`Unknown command: ${command}`);
        showHelp();
        process.exit(1);
    }
  } catch (error) {
    console.error("CLI execution failed:", error);
    process.exit(1);
  } finally {
    cli.shutdown();
  }
}

// Run if this file is executed directly
if (require.main === module) {
  main().catch(console.error);
}

export { ProofChainCLI, parseArgs, showHelp };

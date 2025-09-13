#!/usr/bin/env ts-node

import { DevelopmentOracle } from "./DevelopmentOracle";
import fs from "node:fs";
import path from "node:path";

/**
 * Development Oracle CLI
 * 
 * Real-time oracle validation for developers working on hologram and data functions.
 * Provides immediate feedback on oracle compliance and suggestions for improvements.
 */

function printUsage() {
  console.log(`
Development Oracle CLI

Usage:
  ts-node dev-oracle-cli.ts <command> [options]

Commands:
  validate <file>                    # Validate a specific file
  validate-function <code> <name>    # Validate function code
  report <directory>                 # Get compliance report for directory
  stats                             # Get validation statistics
  watch <directory>                 # Watch directory for changes
  help                              # Show this help message

Options:
  --type <hologram|data>            # Specify function type
  --threshold <number>              # Set oracle threshold (default: 0.95)
  --verbose                         # Show detailed output

Examples:
  ts-node dev-oracle-cli.ts validate src/my-function.ts
  ts-node dev-oracle-cli.ts validate-function "function test() { return 'hello'; }" test
  ts-node dev-oracle-cli.ts report src/
  ts-node dev-oracle-cli.ts watch src/ --type hologram
`);
}

function formatValidationResult(result: any, fileName: string): void {
  const status = result.valid ? '✅ PASS' : '❌ FAIL';
  const score = (result.score * 100).toFixed(1);
  
  console.log(`\n${status} ${fileName}`);
  console.log(`Oracle Score: ${score}%`);
  
  if (result.violations.length > 0) {
    console.log(`\nViolations (${result.violations.length}):`);
    result.violations.forEach((violation: any) => {
      const severity = violation.severity.toUpperCase();
      const type = violation.type.replace(/_/g, ' ');
      const location = violation.location ? ` (${violation.location})` : '';
      
      console.log(`  [${severity}] ${type}${location}: ${violation.message}`);
    });
  }
  
  if (result.suggestions.length > 0) {
    console.log(`\nSuggestions:`);
    result.suggestions.forEach((suggestion: string, index: number) => {
      console.log(`  ${index + 1}. ${suggestion}`);
    });
  }
}

function validateFile(devOracle: DevelopmentOracle, filePath: string): void {
  console.log(`🔍 Validating file: ${filePath}`);
  
  if (!fs.existsSync(filePath)) {
    console.error(`❌ File not found: ${filePath}`);
    return;
  }
  
  const result = devOracle.validateFile(filePath);
  formatValidationResult(result, filePath);
}

function validateFunction(devOracle: DevelopmentOracle, code: string, functionName: string, type?: string): void {
  console.log(`🔍 Validating function: ${functionName}`);
  
  let result;
  if (type === 'hologram') {
    result = devOracle.validateHologramFunction(code, functionName);
  } else if (type === 'data') {
    result = devOracle.validateDataFunction(code, functionName);
  } else {
    result = devOracle.validateNewCode(code, functionName, functionName);
  }
  
  formatValidationResult(result, functionName);
}

function generateReport(devOracle: DevelopmentOracle, directory: string): void {
  console.log(`📊 Generating compliance report for: ${directory}`);
  
  const report = devOracle.getComplianceReport(directory);
  
  console.log(`\n📈 Oracle Compliance Report`);
  console.log(`Total Files: ${report.totalFiles}`);
  console.log(`Compliant Files: ${report.compliantFiles}`);
  console.log(`Non-Compliant Files: ${report.nonCompliantFiles.length}`);
  console.log(`Average Score: ${(report.averageScore * 100).toFixed(1)}%`);
  
  if (report.nonCompliantFiles.length > 0) {
    console.log(`\n❌ Non-Compliant Files:`);
    report.nonCompliantFiles.forEach(file => {
      console.log(`  - ${file}`);
    });
  }
  
  if (report.recommendations.length > 0) {
    console.log(`\n💡 Recommendations:`);
    report.recommendations.forEach((rec, index) => {
      console.log(`  ${index + 1}. ${rec}`);
    });
  }
}

function showStats(devOracle: DevelopmentOracle): void {
  console.log(`📊 Oracle Validation Statistics`);
  
  const stats = devOracle.getStats();
  
  console.log(`Cache Size: ${stats.cacheSize}`);
  console.log(`Validation Count: ${stats.validationCount}`);
  console.log(`Average Score: ${(stats.averageScore * 100).toFixed(1)}%`);
}

function watchDirectory(devOracle: DevelopmentOracle, directory: string, type?: string): void {
  console.log(`👀 Watching directory: ${directory}`);
  console.log(`Function Type: ${type || 'auto-detect'}`);
  console.log(`Press Ctrl+C to stop watching\n`);
  
  // Simple file watching (in a real implementation, you'd use fs.watch)
  const files = getFilesInDirectory(directory);
  
  console.log(`Found ${files.length} files to monitor:`);
  files.forEach(file => {
    console.log(`  - ${file}`);
  });
  
  // In a real implementation, you would set up file watching here
  console.log(`\n💡 Tip: Use a file watcher or IDE integration for real-time validation`);
}

function getFilesInDirectory(dir: string): string[] {
  const files: string[] = [];
  
  try {
    const items = fs.readdirSync(dir);
    
    for (const item of items) {
      const fullPath = path.join(dir, item);
      const stat = fs.statSync(fullPath);
      
      if (stat.isDirectory()) {
        files.push(...getFilesInDirectory(fullPath));
      } else if (stat.isFile() && (item.endsWith('.ts') || item.endsWith('.js') || item.endsWith('.json'))) {
        files.push(fullPath);
      }
    }
  } catch (error) {
    console.error(`Error reading directory: ${error}`);
  }
  
  return files;
}

function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0 || args.includes('--help') || args.includes('help')) {
    printUsage();
    process.exit(0);
  }
  
  const devOracle = new DevelopmentOracle();
  const command = args[0];
  
  // Parse options
  const typeIndex = args.indexOf('--type');
  const type = typeIndex !== -1 && args[typeIndex + 1] ? args[typeIndex + 1] : undefined;
  
  const thresholdIndex = args.indexOf('--threshold');
  const threshold = thresholdIndex !== -1 && args[thresholdIndex + 1] ? parseFloat(args[thresholdIndex + 1]) : 0.95;
  
  const verbose = args.includes('--verbose');
  
  switch (command) {
    case 'validate':
      if (args.length < 2) {
        console.error('❌ File path required for validate command');
        printUsage();
        process.exit(1);
      }
      validateFile(devOracle, args[1]);
      break;
      
    case 'validate-function':
      if (args.length < 3) {
        console.error('❌ Code and function name required for validate-function command');
        printUsage();
        process.exit(1);
      }
      validateFunction(devOracle, args[1], args[2], type);
      break;
      
    case 'report':
      if (args.length < 2) {
        console.error('❌ Directory path required for report command');
        printUsage();
        process.exit(1);
      }
      generateReport(devOracle, args[1]);
      break;
      
    case 'stats':
      showStats(devOracle);
      break;
      
    case 'watch':
      if (args.length < 2) {
        console.error('❌ Directory path required for watch command');
        printUsage();
        process.exit(1);
      }
      watchDirectory(devOracle, args[1], type);
      break;
      
    default:
      console.error(`❌ Unknown command: ${command}`);
      printUsage();
      process.exit(1);
  }
}

if (require.main === module) {
  main();
}

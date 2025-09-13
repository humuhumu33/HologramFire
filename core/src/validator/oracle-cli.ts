#!/usr/bin/env ts-node

import { HologramOracle } from "./HologramOracle";
import path from "node:path";
import fs from "node:fs";

/**
 * CLI for hologram oracle validation
 * 
 * Usage:
 *   ts-node oracle-cli.ts <file>           # Validate module
 *   ts-node oracle-cli.ts --blueprint <file>  # Validate blueprint
 *   ts-node oracle-cli.ts --all           # Validate all modules and blueprint
 */

function printUsage() {
  console.log(`
Hologram Oracle Validator CLI

Usage:
  npm run validate:oracle <module-file>           # Validate module oracle
  npm run validate:oracle:blueprint <blueprint>  # Validate blueprint oracle
  npm run validate:oracle --all                  # Validate all files

Options:
  --blueprint    Validate as blueprint instead of module
  --all          Validate all modules and blueprint
  --threshold    Set oracle threshold (default: 0.95)
  --verbose      Show detailed violation information
  --help         Show this help message

Examples:
  npm run validate:oracle modules/example-good.json
  npm run validate:oracle:blueprint atlas-12288/blueprint/blueprint.json
  npm run validate:oracle --all --verbose
`);
}

function formatViolation(violation: any): string {
  const severity = violation.severity.toUpperCase();
  const type = violation.type.replace(/_/g, ' ');
  const location = violation.location ? ` (${violation.location})` : '';
  
  return `  [${severity}] ${type}${location}: ${violation.message}`;
}

function formatResult(result: any, filePath: string): void {
  const status = result.ok ? '✅ PASS' : '❌ FAIL';
  const score = (result.oracle_score * 100).toFixed(1);
  
  console.log(`\n${status} ${filePath}`);
  console.log(`Oracle Score: ${score}%`);
  console.log(`Holographic Fingerprint: ${result.holographic_fingerprint}`);
  
  if (result.violations.length > 0) {
    console.log(`\nViolations (${result.violations.length}):`);
    result.violations.forEach((violation: any) => {
      console.log(formatViolation(violation));
    });
  }
}

function validateFile(filePath: string, isBlueprint: boolean = false): boolean {
  const validator = new HologramOracle();
  const resolvedPath = path.resolve(filePath);
  
  if (!fs.existsSync(resolvedPath)) {
    console.error(`❌ File not found: ${resolvedPath}`);
    return false;
  }
  
  let result;
  if (isBlueprint) {
    result = validator.validateBlueprint(resolvedPath);
  } else {
    result = validator.validateModule(resolvedPath);
  }
  
  formatResult(result, filePath);
  return result.ok;
}

function validateAllFiles(): boolean {
  console.log('🔍 Validating all modules and blueprint for hologram oracle...\n');
  
  const validator = new HologramOracle();
  let allPassed = true;
  
  // Validate modules
  const modulesDir = path.resolve('data/modules');
  if (fs.existsSync(modulesDir)) {
    const moduleFiles = fs.readdirSync(modulesDir)
      .filter(file => file.endsWith('.json'))
      .map(file => path.join(modulesDir, file));
    
    console.log('📦 Validating modules:');
    for (const moduleFile of moduleFiles) {
      const result = validator.validateModule(moduleFile);
      formatResult(result, path.relative(process.cwd(), moduleFile));
      if (!result.ok) allPassed = false;
    }
  }
  
  // Validate blueprint
  const blueprintPath = path.resolve('atlas-12288/blueprint/blueprint.json');
  if (fs.existsSync(blueprintPath)) {
    console.log('\n📋 Validating blueprint:');
    const result = validator.validateBlueprint(blueprintPath);
    formatResult(result, path.relative(process.cwd(), blueprintPath));
    if (!result.ok) allPassed = false;
  }
  
  return allPassed;
}

function main() {
  const args = process.argv.slice(2);
  
  if (args.includes('--help') || args.length === 0) {
    printUsage();
    process.exit(0);
  }
  
  const isBlueprint = args.includes('--blueprint');
  const validateAll = args.includes('--all');
  const verbose = args.includes('--verbose');
  
  // Set oracle threshold if provided
  const thresholdIndex = args.indexOf('--threshold');
  let threshold = 0.95;
  if (thresholdIndex !== -1 && args[thresholdIndex + 1]) {
    threshold = parseFloat(args[thresholdIndex + 1]);
  }
  
  if (validateAll) {
    const success = validateAllFiles();
    process.exit(success ? 0 : 1);
  }
  
  // Find the file argument (not a flag)
  const fileArg = args.find(arg => !arg.startsWith('--'));
  if (!fileArg) {
    console.error('❌ No file specified');
    printUsage();
    process.exit(1);
  }
  
  const success = validateFile(fileArg, isBlueprint);
  process.exit(success ? 0 : 1);
}

if (require.main === module) {
  main();
}

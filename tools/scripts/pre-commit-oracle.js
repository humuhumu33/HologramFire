#!/usr/bin/env node

/**
 * Pre-commit Oracle Validation Hook
 * 
 * This script automatically validates any new hologram or data functions
 * against the hologram_generator_mini oracle to ensure coherence.
 */

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

// Oracle validation threshold
const ORACLE_THRESHOLD = 0.95;

function log(message, type = 'info') {
  const timestamp = new Date().toISOString();
  const prefix = type === 'error' ? '❌' : type === 'warning' ? '⚠️' : '✅';
  console.log(`${prefix} [${timestamp}] ${message}`);
}

function runOracleValidation() {
  log('🔍 Running oracle validation for new code...');
  
  try {
    // Run oracle validation on all files
    const result = execSync('npm run validate:oracle --all', { 
      encoding: 'utf8',
      stdio: 'pipe'
    });
    
    log('Oracle validation completed successfully');
    return true;
    
  } catch (error) {
    log(`Oracle validation failed: ${error.message}`, 'error');
    
    // Check if it's a threshold issue
    if (error.stdout && error.stdout.includes('Oracle Score:')) {
      const scoreMatch = error.stdout.match(/Oracle Score: ([\d.]+)%/);
      if (scoreMatch) {
        const score = parseFloat(scoreMatch[1]) / 100;
        if (score < ORACLE_THRESHOLD) {
          log(`Oracle score ${(score * 100).toFixed(1)}% is below threshold ${(ORACLE_THRESHOLD * 100).toFixed(1)}%`, 'error');
          log('Please ensure all new hologram and data functions maintain coherence with hologram_generator_mini', 'error');
        }
      }
    }
    
    return false;
  }
}

function validateNewFiles() {
  log('🔍 Validating new files for oracle compliance...');
  
  try {
    // Get list of staged files
    const stagedFiles = execSync('git diff --cached --name-only', { encoding: 'utf8' })
      .trim()
      .split('\n')
      .filter(file => file.length > 0);
    
    if (stagedFiles.length === 0) {
      log('No staged files to validate');
      return true;
    }
    
    log(`Found ${stagedFiles.length} staged files to validate`);
    
    // Check for hologram and data related files
    const hologramFiles = stagedFiles.filter(file => 
      file.includes('hologram') || 
      file.includes('data') || 
      file.includes('oracle') ||
      file.includes('modules') ||
      file.includes('blueprint')
    );
    
    if (hologramFiles.length > 0) {
      log(`Found ${hologramFiles.length} hologram/data related files that require oracle validation`);
      
      // Run oracle validation on these specific files
      for (const file of hologramFiles) {
        if (fs.existsSync(file)) {
          log(`Validating ${file}...`);
          
          try {
            let command;
            if (file.includes('blueprint')) {
              command = `npm run validate:oracle:blueprint ${file}`;
            } else if (file.endsWith('.json')) {
              command = `npm run validate:oracle ${file}`;
            } else {
              // For other files, run general validation
              command = `npm run validate:oracle --all`;
            }
            
            execSync(command, { stdio: 'pipe' });
            log(`✅ ${file} passed oracle validation`);
            
          } catch (error) {
            log(`❌ ${file} failed oracle validation`, 'error');
            log(`Error: ${error.message}`, 'error');
            return false;
          }
        }
      }
    }
    
    return true;
    
  } catch (error) {
    log(`Error validating new files: ${error.message}`, 'error');
    return false;
  }
}

function checkOracleRequirements() {
  log('🔍 Checking oracle requirements...');
  
  // Check if oracle CLI exists
  const oracleCliPath = path.join(__dirname, '..', 'src', 'validator', 'oracle-cli.ts');
  if (!fs.existsSync(oracleCliPath)) {
    log('Oracle CLI not found. Please ensure oracle system is properly installed.', 'error');
    return false;
  }
  
  // Check if oracle validator exists
  const oracleValidatorPath = path.join(__dirname, '..', 'src', 'validator', 'HologramOracle.ts');
  if (!fs.existsSync(oracleValidatorPath)) {
    log('Oracle validator not found. Please ensure oracle system is properly installed.', 'error');
    return false;
  }
  
  log('Oracle requirements satisfied');
  return true;
}

function main() {
  log('🚀 Starting pre-commit oracle validation...');
  
  // Check oracle requirements
  if (!checkOracleRequirements()) {
    process.exit(1);
  }
  
  // Validate new files
  if (!validateNewFiles()) {
    log('❌ Pre-commit validation failed. Please fix oracle violations before committing.', 'error');
    process.exit(1);
  }
  
  // Run full oracle validation
  if (!runOracleValidation()) {
    log('❌ Oracle validation failed. Please ensure all code maintains coherence with hologram_generator_mini.', 'error');
    process.exit(1);
  }
  
  log('✅ All oracle validations passed. Proceeding with commit.');
  process.exit(0);
}

// Run the validation
if (require.main === module) {
  main();
}

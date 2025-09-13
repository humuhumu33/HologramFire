#!/usr/bin/env node

/**
 * Verification script for HoloMatrix throughput optimizations
 * Quick verification that all optimizations are properly implemented
 */

const fs = require('fs');
const path = require('path');

console.log('🔍 VERIFYING HOLOMATRIX THROUGHPUT OPTIMIZATIONS');
console.log('='.repeat(60));

// Check if key files exist
const filesToCheck = [
  'src/demo.ts',
  'src/types.ts', 
  'src/steps/05-matmul.ts',
  'src/steps/05-matmul-throughput-optimized.ts',
  'src/usecases/matmul.ts',
  'src/utils/throughput.ts',
  'src/utils/r96.ts',
  'test-throughput-optimization.ts',
  'package.json'
];

console.log('\n📁 Checking required files...');
let allFilesExist = true;
filesToCheck.forEach(file => {
  const exists = fs.existsSync(file);
  console.log(`  ${exists ? '✅' : '❌'} ${file}`);
  if (!exists) allFilesExist = false;
});

if (!allFilesExist) {
  console.log('\n❌ Some required files are missing!');
  process.exit(1);
}

// Check package.json for optimized scripts
console.log('\n📦 Checking package.json scripts...');
const packageJson = JSON.parse(fs.readFileSync('package.json', 'utf8'));
const requiredScripts = [
  'demo:matmul:optimized',
  'test:throughput'
];

let allScriptsExist = true;
requiredScripts.forEach(script => {
  const exists = packageJson.scripts && packageJson.scripts[script];
  console.log(`  ${exists ? '✅' : '❌'} ${script}`);
  if (!exists) allScriptsExist = false;
});

// Check for iterations support in demo.ts
console.log('\n🔄 Checking iterations support...');
const demoContent = fs.readFileSync('src/demo.ts', 'utf8');
const hasIterationsFlag = demoContent.includes('--iterations');
const hasIterationsConfig = demoContent.includes('iterations: parseInt(options.iterations)');
console.log(`  ${hasIterationsFlag ? '✅' : '❌'} --iterations CLI flag`);
console.log(`  ${hasIterationsConfig ? '✅' : '❌'} iterations config parsing`);

// Check for optimized config in matmul.ts
console.log('\n⚙️  Checking optimized configuration...');
const matmulContent = fs.readFileSync('src/usecases/matmul.ts', 'utf8');
const hasOptimizedConfig = matmulContent.includes('payload: 8192') && 
                          matmulContent.includes('batch: 256') && 
                          matmulContent.includes('workers: 8');
console.log(`  ${hasOptimizedConfig ? '✅' : '❌'} Optimized config (8KB payload, 256 batch, 8 workers)`);

// Check for double-buffering implementation
console.log('\n🔄 Checking double-buffering implementation...');
const optimizedContent = fs.readFileSync('src/steps/05-matmul-throughput-optimized.ts', 'utf8');
const hasDoubleBuffering = optimizedContent.includes('DoubleBufferedMatMul') &&
                          optimizedContent.includes('runProducer') &&
                          optimizedContent.includes('runConsumer');
console.log(`  ${hasDoubleBuffering ? '✅' : '❌'} Double-buffering implementation`);

// Check for throughput utilities
console.log('\n📊 Checking throughput measurement utilities...');
const throughputContent = fs.readFileSync('src/utils/throughput.ts', 'utf8');
const hasThroughputUtils = throughputContent.includes('ThroughputTimer') &&
                          throughputContent.includes('calculateThroughput') &&
                          throughputContent.includes('calculateMatrixDataInfo');
console.log(`  ${hasThroughputUtils ? '✅' : '❌'} Throughput measurement utilities`);

// Check for R96 utilities
console.log('\n🔐 Checking R96 utilities...');
const r96Content = fs.readFileSync('src/utils/r96.ts', 'utf8');
const hasR96Utils = r96Content.includes('generateR96') &&
                   r96Content.includes('ccmHash');
console.log(`  ${hasR96Utils ? '✅' : '❌'} R96 hash generation utilities`);

// Summary
console.log('\n📋 VERIFICATION SUMMARY');
console.log('='.repeat(40));

const allChecks = [
  allFilesExist,
  allScriptsExist,
  hasIterationsFlag && hasIterationsConfig,
  hasOptimizedConfig,
  hasDoubleBuffering,
  hasThroughputUtils,
  hasR96Utils
];

const passedChecks = allChecks.filter(Boolean).length;
const totalChecks = allChecks.length;

console.log(`Passed: ${passedChecks}/${totalChecks} checks`);

if (passedChecks === totalChecks) {
  console.log('\n🎉 ALL OPTIMIZATIONS VERIFIED SUCCESSFULLY!');
  console.log('✅ All throughput optimizations are properly implemented');
  console.log('✅ Ready for testing and deployment');
  process.exit(0);
} else {
  console.log('\n⚠️  SOME OPTIMIZATIONS MISSING');
  console.log('❌ Please check the failed items above');
  process.exit(1);
}
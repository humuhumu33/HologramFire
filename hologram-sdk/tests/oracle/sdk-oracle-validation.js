#!/usr/bin/env node

/**
 * Oracle Validation Suite for Hologram SDK Components
 * 
 * This test suite validates all new SDK components against the hologram_generator_mini
 * oracle to ensure holographic coherence and compliance with Atlas-12288 standards.
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

class SDKOracleValidator {
  constructor() {
    this.testResults = {
      timestamp: new Date().toISOString(),
      sdk_components: {},
      overall_coherence_score: 0,
      violations: [],
      recommendations: []
    };
    
    this.oracleThreshold = 0.95;
    this.criticalThreshold = 0.8;
  }

  /**
   * Main validation entry point
   */
  async validateAll() {
    console.log('🔮 Hologram SDK Oracle Validation Suite');
    console.log('=' * 50);
    
    const modules = [
      'modules/hologram-engine.json',
      'modules/hologram-docker-python.json', 
      'modules/hologram-native-python.json'
    ];
    
    let totalScore = 0;
    let validModules = 0;
    
    for (const modulePath of modules) {
      if (fs.existsSync(modulePath)) {
        console.log(`\n📋 Validating: ${modulePath}`);
        
        try {
          const result = await this.validateModule(modulePath);
          this.testResults.sdk_components[modulePath] = result;
          
          if (result.ok) {
            validModules++;
            console.log(`  ✅ PASS - Oracle Score: ${result.oracle_score.toFixed(3)}`);
          } else {
            console.log(`  ❌ FAIL - Oracle Score: ${result.oracle_score.toFixed(3)}`);
            console.log(`  📊 Violations: ${result.violations.length}`);
            
            // Log critical violations
            const criticalViolations = result.violations.filter(v => v.severity === 'critical');
            if (criticalViolations.length > 0) {
              console.log(`  🚨 Critical Violations:`);
              criticalViolations.forEach(v => {
                console.log(`    - ${v.type}: ${v.message}`);
              });
            }
          }
          
          totalScore += result.oracle_score;
          
        } catch (error) {
          console.log(`  💥 ERROR: ${error.message}`);
          this.testResults.sdk_components[modulePath] = {
            ok: false,
            oracle_score: 0,
            error: error.message,
            violations: [{
              type: 'validation_error',
              severity: 'critical',
              message: error.message
            }]
          };
        }
      } else {
        console.log(`  ⚠️  Module not found: ${modulePath}`);
      }
    }
    
    // Calculate overall coherence score
    this.testResults.overall_coherence_score = modules.length > 0 ? totalScore / modules.length : 0;
    
    // Generate recommendations
    this.generateRecommendations();
    
    // Output results
    this.outputResults();
    
    return this.testResults.overall_coherence_score >= this.oracleThreshold;
  }

  /**
   * Validate a single module against hologram_generator_mini oracle
   */
  async validateModule(modulePath) {
    try {
      // Run hologram_generator_mini validation
      const result = execSync(`python hologram_generator_mini.py ${modulePath}`, {
        encoding: 'utf8',
        timeout: 10000
      });
      
      // Parse the JSON result
      const validationResult = JSON.parse(result);
      
      return {
        ok: validationResult.ok,
        oracle_score: validationResult.oracle_score,
        violations: validationResult.violations || [],
        holographic_fingerprint: validationResult.holographic_fingerprint,
        execution_time_ms: validationResult.execution_time_ms,
        timestamp: validationResult.timestamp
      };
      
    } catch (error) {
      throw new Error(`Oracle validation failed: ${error.message}`);
    }
  }

  /**
   * Generate recommendations based on validation results
   */
  generateRecommendations() {
    const allViolations = [];
    
    // Collect all violations from all modules
    Object.values(this.testResults.sdk_components).forEach(component => {
      if (component.violations) {
        allViolations.push(...component.violations);
      }
    });
    
    // Analyze violation patterns
    const violationTypes = {};
    allViolations.forEach(violation => {
      if (!violationTypes[violation.type]) {
        violationTypes[violation.type] = { count: 0, severity: violation.severity };
      }
      violationTypes[violation.type].count++;
    });
    
    // Generate recommendations
    if (violationTypes.holographic_correspondence) {
      this.testResults.recommendations.push({
        type: 'holographic_correspondence',
        priority: 'critical',
        message: 'Implement proper holographic correspondence with hologram_generator_mini reference',
        action: 'Add holographic_correspondence invariants to all modules'
      });
    }
    
    if (violationTypes.resonance_classification) {
      this.testResults.recommendations.push({
        type: 'resonance_classification',
        priority: 'high',
        message: 'Implement resonance classification for harmonic frequency management',
        action: 'Add resonance_classification with proper harmonic frequencies'
      });
    }
    
    if (violationTypes.cycle_conservation) {
      this.testResults.recommendations.push({
        type: 'cycle_conservation',
        priority: 'high',
        message: 'Implement cycle conservation for energy efficiency',
        action: 'Add cycle_conservation with proper conservation factors'
      });
    }
    
    if (violationTypes.page_conservation) {
      this.testResults.recommendations.push({
        type: 'page_conservation',
        priority: 'medium',
        message: 'Implement page conservation for memory efficiency',
        action: 'Add page_conservation with proper memory alignment'
      });
    }
    
    // Store violation analysis
    this.testResults.violations = Object.entries(violationTypes).map(([type, data]) => ({
      type,
      count: data.count,
      severity: data.severity
    }));
  }

  /**
   * Output validation results
   */
  outputResults() {
    console.log('\n' + '=' * 50);
    console.log('📊 ORACLE VALIDATION RESULTS');
    console.log('=' * 50);
    
    console.log(`Overall Coherence Score: ${this.testResults.overall_coherence_score.toFixed(3)}`);
    console.log(`Oracle Threshold: ${this.oracleThreshold}`);
    console.log(`Status: ${this.testResults.overall_coherence_score >= this.oracleThreshold ? '✅ PASS' : '❌ FAIL'}`);
    
    if (this.testResults.violations.length > 0) {
      console.log('\n🚨 VIOLATIONS SUMMARY:');
      this.testResults.violations.forEach(violation => {
        console.log(`  ${violation.type}: ${violation.count} (${violation.severity})`);
      });
    }
    
    if (this.testResults.recommendations.length > 0) {
      console.log('\n💡 RECOMMENDATIONS:');
      this.testResults.recommendations.forEach(rec => {
        console.log(`  [${rec.priority.toUpperCase()}] ${rec.message}`);
        console.log(`    Action: ${rec.action}`);
      });
    }
    
    // Save detailed results
    const reportPath = 'sdk-oracle-validation-report.json';
    fs.writeFileSync(reportPath, JSON.stringify(this.testResults, null, 2));
    console.log(`\n📄 Detailed report saved to: ${reportPath}`);
  }

  /**
   * Validate specific SDK components
   */
  async validateEngine() {
    console.log('🔧 Validating Hologram Engine...');
    return await this.validateModule('modules/hologram-engine.json');
  }

  async validateDockerPython() {
    console.log('🐍 Validating Hologram Docker Python...');
    return await this.validateModule('modules/hologram-docker-python.json');
  }

  async validateNativePython() {
    console.log('🐍 Validating Hologram Native Python...');
    return await this.validateModule('modules/hologram-native-python.json');
  }
}

// CLI interface
if (require.main === module) {
  const validator = new SDKOracleValidator();
  
  const args = process.argv.slice(2);
  if (args.length === 0) {
    // Run full validation suite
    validator.validateAll().then(success => {
      process.exit(success ? 0 : 1);
    });
  } else {
    // Run specific validation
    const component = args[0];
    switch (component) {
      case 'engine':
        validator.validateEngine().then(result => {
          console.log(JSON.stringify(result, null, 2));
          process.exit(result.ok ? 0 : 1);
        });
        break;
      case 'docker-python':
        validator.validateDockerPython().then(result => {
          console.log(JSON.stringify(result, null, 2));
          process.exit(result.ok ? 0 : 1);
        });
        break;
      case 'native-python':
        validator.validateNativePython().then(result => {
          console.log(JSON.stringify(result, null, 2));
          process.exit(result.ok ? 0 : 1);
        });
        break;
      default:
        console.error(`Unknown component: ${component}`);
        console.error('Available components: engine, docker-python, native-python');
        process.exit(1);
    }
  }
}

module.exports = SDKOracleValidator;

/**
 * Validation Script for Quantum-Resistant Cryptographic System
 * 
 * This script validates the quantum-resistant cryptographic system implementation
 * and ensures it meets all requirements for conservation and coherence principles.
 */

import { 
  getQuantumResistantCryptoSystem,
  createQuantumResistantKeyPair,
  encryptQuantumResistant,
  decryptQuantumResistant,
  signQuantumResistant,
  verifyQuantumResistant,
  authenticateQuantumResistant,
  dataToField,
  fieldToData,
  validateFieldDimensions,
  createTestField
} from "../../src/crypto/quantum-resistant/index";

import {
  getQuantumResistantUpgrade,
  upgradeToQuantumResistant
} from "../../src/crypto/quantum-resistant/QuantumResistantUpgrade";

interface ValidationResult {
  test_name: string;
  passed: boolean;
  error?: string;
  performance_ms: number;
  details: any;
}

interface ValidationReport {
  total_tests: number;
  passed_tests: number;
  failed_tests: number;
  total_time_ms: number;
  results: ValidationResult[];
  system_health: string;
  recommendations: string[];
}

/**
 * Quantum-Resistant System Validator
 */
export class QuantumResistantValidator {
  private results: ValidationResult[] = [];
  private startTime: number = 0;

  /**
   * Run complete validation suite
   */
  async runValidationSuite(): Promise<ValidationReport> {
    this.startTime = performance.now();
    this.results = [];

    console.log("🔬 Starting Quantum-Resistant Cryptographic System Validation");
    console.log("=" .repeat(60));

    // Core system validation
    await this.validateCoreSystem();
    await this.validateConservationPrinciples();
    await this.validateCoherencePrinciples();
    await this.validateHolographicCorrespondence();
    await this.validateQuantumResistance();
    await this.validatePerformance();
    await this.validateIntegration();
    await this.validateMigration();

    const totalTime = performance.now() - this.startTime;
    const passedTests = this.results.filter(r => r.passed).length;
    const failedTests = this.results.filter(r => !r.passed).length;

    const report: ValidationReport = {
      total_tests: this.results.length,
      passed_tests: passedTests,
      failed_tests: failedTests,
      total_time_ms: totalTime,
      results: this.results,
      system_health: this.calculateSystemHealth(),
      recommendations: this.generateRecommendations()
    };

    this.printReport(report);
    return report;
  }

  /**
   * Validate core system functionality
   */
  private async validateCoreSystem(): Promise<void> {
    console.log("\n🔧 Validating Core System...");

    await this.runTest("Key Generation", async () => {
      const keyPair = await createQuantumResistantKeyPair("test_seed", { test: true });
      
      if (!keyPair.fieldKey) throw new Error("Field key not generated");
      if (!keyPair.publicKey) throw new Error("Public key not generated");
      if (!keyPair.privateKey) throw new Error("Private key not generated");
      
      return { keyPair };
    });

    await this.runTest("Field Dimensions", async () => {
      const testField = createTestField();
      const isValid = validateFieldDimensions(testField);
      
      if (!isValid) throw new Error("Field dimensions invalid");
      
      return { testField, isValid };
    });

    await this.runTest("Data Conversion", async () => {
      const testData = { message: "test", numbers: [1, 2, 3] };
      const field = dataToField(testData);
      const convertedData = fieldToData(field);
      
      if (JSON.stringify(testData) !== JSON.stringify(convertedData)) {
        throw new Error("Data conversion failed");
      }
      
      return { testData, field, convertedData };
    });
  }

  /**
   * Validate conservation principles
   */
  private async validateConservationPrinciples(): Promise<void> {
    console.log("\n⚖️ Validating Conservation Principles...");

    await this.runTest("C768 Conservation", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("conservation_test", {});
      
      // Test C768 schedule conservation
      const schedule = keyPair.fieldKey.c768_schedule;
      const seen = new Set<number>();
      let sum = 0;
      
      for (const value of schedule || []) {
        if (seen.has(value)) throw new Error("C768 schedule has duplicates");
        seen.add(value);
        sum += value;
      }
      
      const expectedSum = (768 * (768 - 1)) / 2;
      if (sum !== expectedSum) throw new Error("C768 schedule sum incorrect");
      
      return { schedule, sum, expectedSum };
    });

    await this.runTest("Field Conservation", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("field_conservation_test", {});
      
      // Test field conservation
      const conservation = keyPair.fieldKey.field.conservation;
      if (conservation < 0.9) throw new Error("Field conservation too low");
      
      return { conservation };
    });

    await this.runTest("Resonance Conservation", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("resonance_conservation_test", {});
      
      // Test resonance spectrum conservation
      const resonance = keyPair.fieldKey.field.resonance;
      const sum = resonance.reduce((a: number, b: number) => a + b, 0);
      
      if (Math.abs(sum - 1.0) > 0.01) throw new Error("Resonance spectrum not normalized");
      
      return { resonance, sum };
    });
  }

  /**
   * Validate coherence principles
   */
  private async validateCoherencePrinciples(): Promise<void> {
    console.log("\n🌊 Validating Coherence Principles...");

    await this.runTest("Field Coherence", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("coherence_test", {});
      
      const coherence = keyPair.fieldKey.field.coherence;
      if (coherence < 0.9) throw new Error("Field coherence too low");
      
      return { coherence };
    });

    await this.runTest("Signature Coherence", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("signature_coherence_test", {});
      const message = { test: "coherence_message" };
      
      const signature = await system.sign(message, keyPair.fieldKey);
      if ((signature.field_coherence ?? 0) < 0.9) throw new Error("Signature coherence too low");
      
      return { signature };
    });

    await this.runTest("Encryption Coherence", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("encryption_coherence_test", {});
      const plaintext = createTestField();
      
      const ciphertext = await system.encrypt(plaintext, keyPair.fieldKey, {});
      const decrypted = await system.decrypt(ciphertext, keyPair.fieldKey, {});
      
      if (decrypted.coherence_score < 0.9) throw new Error("Encryption coherence too low");
      
      return { ciphertext, decrypted };
    });
  }

  /**
   * Validate holographic correspondence
   */
  private async validateHolographicCorrespondence(): Promise<void> {
    console.log("\n🔮 Validating Holographic Correspondence...");

    await this.runTest("Holographic Fingerprint", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("holographic_test", {});
      
      const fingerprint = keyPair.fieldKey.field.holographic_fingerprint;
      if (!fingerprint || fingerprint.length === 0) {
        throw new Error("Holographic fingerprint missing");
      }
      
      return { fingerprint };
    });

    await this.runTest("Holographic Correspondence", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("correspondence_test", {});
      
      const correspondence = keyPair.fieldKey.holographic_correspondence;
      if (!correspondence || correspondence.length === 0) {
        throw new Error("Holographic correspondence missing");
      }
      
      return { correspondence };
    });

    await this.runTest("Holographic Signature", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("holographic_signature_test", {});
      const message = { test: "holographic_message" };
      
      const signature = await system.sign(message, keyPair.fieldKey);
      if (!signature.holographic_correspondence) {
        throw new Error("Holographic correspondence in signature missing");
      }
      
      return { signature };
    });
  }

  /**
   * Validate quantum resistance
   */
  private async validateQuantumResistance(): Promise<void> {
    console.log("\n🛡️ Validating Quantum Resistance...");

    await this.runTest("Information Field Security", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("quantum_resistance_test", {});
      
      // Test that security is based on information field properties, not computational hardness
      const field = keyPair.fieldKey.field;
      const security_metrics = {
        coherence: field.coherence,
        conservation: field.conservation,
        resonance_entropy: this.calculateEntropy(field.resonance)
      };
      
      if (security_metrics.coherence < 0.9) throw new Error("Insufficient coherence for quantum resistance");
      if (security_metrics.conservation < 0.9) throw new Error("Insufficient conservation for quantum resistance");
      if (security_metrics.resonance_entropy < 0.8) throw new Error("Insufficient resonance entropy for quantum resistance");
      
      return { security_metrics };
    });

    await this.runTest("Conservation-Based Security", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("conservation_security_test", {});
      
      // Test that security relies on conservation principles
      const conservation_proof = keyPair.fieldKey.field.conservation;
      if (conservation_proof < 0.95) throw new Error("Conservation-based security insufficient");
      
      return { conservation_proof };
    });

    await this.runTest("Coherence-Based Security", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("coherence_security_test", {});
      
      // Test that security relies on coherence principles
      const coherence_proof = keyPair.fieldKey.field.coherence;
      if (coherence_proof < 0.95) throw new Error("Coherence-based security insufficient");
      
      return { coherence_proof };
    });
  }

  /**
   * Validate performance
   */
  private async validatePerformance(): Promise<void> {
    console.log("\n⚡ Validating Performance...");

    await this.runTest("Key Generation Performance", async () => {
      const start = performance.now();
      const keyPair = await createQuantumResistantKeyPair("performance_test", {});
      const duration = performance.now() - start;
      
      if (duration > 1000) throw new Error("Key generation too slow");
      
      return { duration, keyPair };
    });

    await this.runTest("Signature Performance", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("signature_performance_test", {});
      const message = { test: "performance_message" };
      
      const start = performance.now();
      const signature = await system.sign(message, keyPair.fieldKey);
      const duration = performance.now() - start;
      
      if (duration > 500) throw new Error("Signature creation too slow");
      
      return { duration, signature };
    });

    await this.runTest("Encryption Performance", async () => {
      const system = getQuantumResistantCryptoSystem();
      const keyPair = await system.generateKeyPair("encryption_performance_test", {});
      const plaintext = createTestField();
      
      const start = performance.now();
      const ciphertext = await system.encrypt(plaintext, keyPair.fieldKey, {});
      const duration = performance.now() - start;
      
      if (duration > 1000) throw new Error("Encryption too slow");
      
      return { duration, ciphertext };
    });
  }

  /**
   * Validate integration
   */
  private async validateIntegration(): Promise<void> {
    console.log("\n🔗 Validating Integration...");

    await this.runTest("System Integration", async () => {
      const system = getQuantumResistantCryptoSystem();
      
      // Test complete workflow
      const keyPair = await system.generateKeyPair("integration_test", {});
      const message = { test: "integration_message" };
      
      const signature = await system.sign(message, keyPair.fieldKey);
      const verified = await system.verify(message, signature, keyPair.fieldKey);
      
      if (!verified) throw new Error("Signature verification failed");
      
      return { keyPair, signature, verified };
    });

    await this.runTest("Upgrade Integration", async () => {
      const upgrade = await upgradeToQuantumResistant({
        enable_quantum_resistance: true,
        hybrid_mode: false
      });
      
      const input = { test: "upgrade_integration" };
      const result = await upgrade.hybridHash(input, "test_domain");
      
      if (!result.quantum_resistant) throw new Error("Quantum resistance not enabled");
      
      return { upgrade, result };
    });
  }

  /**
   * Validate migration
   */
  private async validateMigration(): Promise<void> {
    console.log("\n🔄 Validating Migration...");

    await this.runTest("Migration Planning", async () => {
      const upgrade = getQuantumResistantUpgrade();
      const plan = upgrade.createMigrationPlan("classical", "quantum_resistant", {
        performance_target: 0.9,
        security_level: 0.95
      });
      
      if (!plan.migration_steps || plan.migration_steps.length === 0) {
        throw new Error("Migration plan has no steps");
      }
      
      return { plan };
    });

    await this.runTest("Migration Execution", async () => {
      const upgrade = getQuantumResistantUpgrade();
      const plan = upgrade.createMigrationPlan("classical", "quantum_resistant");
      
      const result = await upgrade.executeMigration(plan);
      
      if (!result.success) throw new Error("Migration execution failed");
      
      return { result };
    });
  }

  /**
   * Run individual test
   */
  private async runTest(testName: string, testFn: () => Promise<any>): Promise<void> {
    const start = performance.now();
    
    try {
      const details = await testFn();
      const duration = performance.now() - start;
      
      this.results.push({
        test_name: testName,
        passed: true,
        performance_ms: duration,
        details
      });
      
      console.log(`  ✅ ${testName} (${duration.toFixed(2)}ms)`);
    } catch (error) {
      const duration = performance.now() - start;
      
      this.results.push({
        test_name: testName,
        passed: false,
        error: error instanceof Error ? error.message : String(error),
        performance_ms: duration,
        details: {}
      });
      
      console.log(`  ❌ ${testName} (${duration.toFixed(2)}ms): ${error}`);
    }
  }

  /**
   * Calculate system health
   */
  private calculateSystemHealth(): string {
    const passedTests = this.results.filter(r => r.passed).length;
    const totalTests = this.results.length;
    const healthPercentage = (passedTests / totalTests) * 100;
    
    if (healthPercentage >= 95) return "EXCELLENT";
    if (healthPercentage >= 90) return "GOOD";
    if (healthPercentage >= 80) return "FAIR";
    if (healthPercentage >= 70) return "POOR";
    return "CRITICAL";
  }

  /**
   * Generate recommendations
   */
  private generateRecommendations(): string[] {
    const recommendations: string[] = [];
    const failedTests = this.results.filter(r => !r.passed);
    
    if (failedTests.length === 0) {
      recommendations.push("System is fully operational and ready for production use");
    } else {
      recommendations.push("Address failed tests before deploying to production");
      
      const performanceIssues = failedTests.filter(t => t.test_name.includes("Performance"));
      if (performanceIssues.length > 0) {
        recommendations.push("Optimize performance-critical components");
      }
      
      const securityIssues = failedTests.filter(t => t.test_name.includes("Security") || t.test_name.includes("Resistance"));
      if (securityIssues.length > 0) {
        recommendations.push("Review and strengthen security implementations");
      }
    }
    
    return recommendations;
  }

  /**
   * Print validation report
   */
  private printReport(report: ValidationReport): void {
    console.log("\n" + "=".repeat(60));
    console.log("📊 QUANTUM-RESISTANT CRYPTOGRAPHIC SYSTEM VALIDATION REPORT");
    console.log("=".repeat(60));
    
    console.log(`\n📈 Summary:`);
    console.log(`  Total Tests: ${report.total_tests}`);
    console.log(`  Passed: ${report.passed_tests} ✅`);
    console.log(`  Failed: ${report.failed_tests} ❌`);
    console.log(`  Success Rate: ${((report.passed_tests / report.total_tests) * 100).toFixed(1)}%`);
    console.log(`  Total Time: ${report.total_time_ms.toFixed(2)}ms`);
    console.log(`  System Health: ${report.system_health}`);
    
    if (report.failed_tests > 0) {
      console.log(`\n❌ Failed Tests:`);
      report.results.filter(r => !r.passed).forEach(result => {
        console.log(`  - ${result.test_name}: ${result.error}`);
      });
    }
    
    console.log(`\n💡 Recommendations:`);
    report.recommendations.forEach(rec => {
      console.log(`  - ${rec}`);
    });
    
    console.log("\n" + "=".repeat(60));
  }

  /**
   * Calculate entropy of a distribution
   */
  private calculateEntropy(distribution: number[]): number {
    let entropy = 0;
    for (const p of distribution) {
      if (p > 0) {
        entropy -= p * Math.log2(p);
      }
    }
    return entropy;
  }
}

/**
 * Main validation function
 */
export async function validateQuantumResistantSystem(): Promise<ValidationReport> {
  const validator = new QuantumResistantValidator();
  return validator.runValidationSuite();
}

// Run validation if this script is executed directly
if (require.main === module) {
  validateQuantumResistantSystem()
    .then(report => {
      process.exit(report.failed_tests > 0 ? 1 : 0);
    })
    .catch(error => {
      console.error("Validation failed:", error);
      process.exit(1);
    });
}

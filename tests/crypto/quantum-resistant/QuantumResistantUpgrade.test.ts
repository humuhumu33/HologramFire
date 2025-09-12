/**
 * Tests for Quantum-Resistant System Upgrade
 * 
 * These tests validate the integration and migration from classical to
 * quantum-resistant cryptographic systems.
 */

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import {
  QuantumResistantUpgrade,
  QuantumResistantUpgradeConfig,
  HybridCryptoResult,
  MigrationPlan,
  getQuantumResistantUpgrade,
  upgradeToQuantumResistant,
  createMigrationPlan,
  executeQuantumResistantMigration
} from "../../../src/crypto/quantum-resistant/QuantumResistantUpgrade";

describe("QuantumResistantUpgrade", () => {
  let upgrade: QuantumResistantUpgrade;
  let config: QuantumResistantUpgradeConfig;

  beforeEach(() => {
    config = {
      enable_quantum_resistance: true,
      hybrid_mode: false,
      migration_threshold: 0.95,
      backward_compatibility: true,
      performance_optimization: true,
      conservation_validation: true,
      coherence_monitoring: true
    };
    upgrade = new QuantumResistantUpgrade(config);
  });

  afterEach(() => {
    // Clean up any resources
  });

  describe("Configuration", () => {
    it("should initialize with default configuration", () => {
      const defaultUpgrade = new QuantumResistantUpgrade();
      const defaultConfig = defaultUpgrade.getConfig();
      
      expect(defaultConfig.enable_quantum_resistance).toBe(true);
      expect(defaultConfig.hybrid_mode).toBe(false);
      expect(defaultConfig.migration_threshold).toBe(0.95);
      expect(defaultConfig.backward_compatibility).toBe(true);
    });

    it("should accept custom configuration", () => {
      const customConfig: QuantumResistantUpgradeConfig = {
        enable_quantum_resistance: false,
        hybrid_mode: true,
        migration_threshold: 0.9,
        backward_compatibility: false,
        performance_optimization: false,
        conservation_validation: false,
        coherence_monitoring: false
      };
      
      const customUpgrade = new QuantumResistantUpgrade(customConfig);
      const actualConfig = customUpgrade.getConfig();
      
      expect(actualConfig.enable_quantum_resistance).toBe(false);
      expect(actualConfig.hybrid_mode).toBe(true);
      expect(actualConfig.migration_threshold).toBe(0.9);
      expect(actualConfig.backward_compatibility).toBe(false);
    });

    it("should update configuration", () => {
      const newConfig = {
        enable_quantum_resistance: false,
        hybrid_mode: true
      };
      
      upgrade.updateConfig(newConfig);
      const updatedConfig = upgrade.getConfig();
      
      expect(updatedConfig.enable_quantum_resistance).toBe(false);
      expect(updatedConfig.hybrid_mode).toBe(true);
      expect(updatedConfig.migration_threshold).toBe(0.95); // Should remain unchanged
    });
  });

  describe("Hybrid Hash Function", () => {
    it("should use quantum-resistant system when enabled", async () => {
      const input = { test: "quantum_hash_test", data: [1, 2, 3] };
      const domain = "test_domain";
      
      const result = await upgrade.hybridHash(input, domain);
      
      expect(result.quantum_resistant).toBe(true);
      expect(result.quantum_result).toBeDefined();
      expect(result.coherence_score).toBeGreaterThan(0);
      expect(result.conservation_verified).toBe(true);
      expect(result.holographic_correspondence).toBeDefined();
      expect(result.performance_metrics.quantum_time_ms).toBeGreaterThan(0);
    });

    it("should use classical system when quantum resistance disabled", async () => {
      upgrade.updateConfig({ enable_quantum_resistance: false });
      
      const input = { test: "classical_hash_test", data: [1, 2, 3] };
      const domain = "test_domain";
      
      const result = await upgrade.hybridHash(input, domain);
      
      expect(result.quantum_resistant).toBe(false);
      expect(result.classical_result).toBeDefined();
      expect(result.quantum_result).toBeUndefined();
      expect(result.performance_metrics.classical_time_ms).toBeGreaterThan(0);
    });

    it("should use both systems in hybrid mode", async () => {
      upgrade.updateConfig({ hybrid_mode: true });
      
      const input = { test: "hybrid_hash_test", data: [1, 2, 3] };
      const domain = "test_domain";
      
      const result = await upgrade.hybridHash(input, domain);
      
      expect(result.quantum_resistant).toBe(true);
      expect(result.classical_result).toBeDefined();
      expect(result.quantum_result).toBeDefined();
      expect(result.performance_metrics.quantum_time_ms).toBeGreaterThan(0);
      expect(result.performance_metrics.classical_time_ms).toBeGreaterThan(0);
    });

    it("should provide performance metrics", async () => {
      const input = { test: "performance_test", data: [1, 2, 3] };
      const domain = "test_domain";
      
      const result = await upgrade.hybridHash(input, domain);
      
      expect(result.performance_metrics).toBeDefined();
      expect(result.performance_metrics.total_time_ms).toBeGreaterThan(0);
      expect(result.performance_metrics.quantum_time_ms).toBeGreaterThan(0);
    });
  });

  describe("Hybrid Signature Function", () => {
    it("should create quantum-resistant signatures", async () => {
      const message = { test: "quantum_signature_test", data: [1, 2, 3] };
      const moduleId = "test_module";
      const secret = "test_secret";
      
      const result = await upgrade.hybridSign(message, moduleId, secret);
      
      expect(result.quantum_resistant).toBe(true);
      expect(result.quantum_result).toBeDefined();
      expect(result.coherence_score).toBeGreaterThan(0);
      expect(result.conservation_verified).toBe(true);
    });

    it("should create classical signatures when quantum resistance disabled", async () => {
      upgrade.updateConfig({ enable_quantum_resistance: false });
      
      const message = { test: "classical_signature_test", data: [1, 2, 3] };
      const moduleId = "test_module";
      const secret = "test_secret";
      
      const result = await upgrade.hybridSign(message, moduleId, secret);
      
      expect(result.quantum_resistant).toBe(false);
      expect(result.classical_result).toBeDefined();
      expect(result.quantum_result).toBeUndefined();
    });

    it("should create hybrid signatures in hybrid mode", async () => {
      upgrade.updateConfig({ hybrid_mode: true });
      
      const message = { test: "hybrid_signature_test", data: [1, 2, 3] };
      const moduleId = "test_module";
      const secret = "test_secret";
      
      const result = await upgrade.hybridSign(message, moduleId, secret);
      
      expect(result.quantum_resistant).toBe(true);
      expect(result.classical_result).toBeDefined();
      expect(result.quantum_result).toBeDefined();
    });
  });

  describe("Hybrid Attestation Function", () => {
    it("should create quantum-resistant attestations", async () => {
      const payload = { test: "quantum_attestation_test", data: [1, 2, 3] };
      const secret = "test_secret";
      
      const result = await upgrade.hybridAttest(payload, secret);
      
      expect(result.quantum_resistant).toBe(true);
      expect(result.quantum_result).toBeDefined();
      expect(result.coherence_score).toBeGreaterThan(0);
      expect(result.conservation_verified).toBe(true);
    });

    it("should create classical attestations when quantum resistance disabled", async () => {
      upgrade.updateConfig({ enable_quantum_resistance: false });
      
      const payload = { test: "classical_attestation_test", data: [1, 2, 3] };
      const secret = "test_secret";
      
      const result = await upgrade.hybridAttest(payload, secret);
      
      expect(result.quantum_resistant).toBe(false);
      expect(result.classical_result).toBeDefined();
      expect(result.quantum_result).toBeUndefined();
    });
  });

  describe("Migration Planning", () => {
    it("should create migration plan", () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      const requirements = {
        performance_target: 0.9,
        security_level: 0.95,
        compatibility_required: true
      };
      
      const plan = upgrade.createMigrationPlan(currentSystem, targetSystem, requirements);
      
      expect(plan).toBeDefined();
      expect(plan.current_system).toBe(currentSystem);
      expect(plan.target_system).toBe(targetSystem);
      expect(plan.migration_steps).toBeDefined();
      expect(plan.migration_steps.length).toBeGreaterThan(0);
      expect(plan.estimated_time_ms).toBeGreaterThan(0);
      expect(plan.risk_assessment).toBeDefined();
      expect(plan.rollback_plan).toBeDefined();
      expect(plan.rollback_plan.length).toBeGreaterThan(0);
    });

    it("should create migration plan with default requirements", () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      
      const plan = upgrade.createMigrationPlan(currentSystem, targetSystem);
      
      expect(plan).toBeDefined();
      expect(plan.current_system).toBe(currentSystem);
      expect(plan.target_system).toBe(targetSystem);
    });

    it("should estimate migration time based on requirements", () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      
      const basicRequirements = {};
      const complexRequirements = {
        performance_target: 0.9,
        security_level: 0.95,
        compatibility_required: true
      };
      
      const basicPlan = upgrade.createMigrationPlan(currentSystem, targetSystem, basicRequirements);
      const complexPlan = upgrade.createMigrationPlan(currentSystem, targetSystem, complexRequirements);
      
      expect(complexPlan.estimated_time_ms).toBeGreaterThan(basicPlan.estimated_time_ms);
    });

    it("should assess migration risk", () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      
      const lowRiskRequirements = {};
      const highRiskRequirements = {
        performance_target: 0.7, // Low performance target
        security_level: 0.98,    // Very high security
        compatibility_required: true
      };
      
      const lowRiskPlan = upgrade.createMigrationPlan(currentSystem, targetSystem, lowRiskRequirements);
      const highRiskPlan = upgrade.createMigrationPlan(currentSystem, targetSystem, highRiskRequirements);
      
      expect(lowRiskPlan.risk_assessment).toContain("LOW");
      expect(highRiskPlan.risk_assessment).toContain("HIGH");
    });
  });

  describe("Migration Execution", () => {
    it("should execute migration plan", async () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      const requirements = {
        performance_target: 0.9,
        security_level: 0.95,
        compatibility_required: true
      };
      
      const plan = upgrade.createMigrationPlan(currentSystem, targetSystem, requirements);
      const result = await upgrade.executeMigration(plan);
      
      expect(result).toBeDefined();
      expect(result.success).toBe(true);
      expect(result.steps_completed).toBe(plan.migration_steps.length);
      expect(result.errors).toHaveLength(0);
      expect(result.performance_impact).toBeGreaterThanOrEqual(0);
    });

    it("should handle migration errors gracefully", async () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      
      const plan = upgrade.createMigrationPlan(currentSystem, targetSystem);
      
      // Simulate error by modifying the plan
      plan.migration_steps = ["invalid_step"];
      
      const result = await upgrade.executeMigration(plan);
      
      expect(result.success).toBe(false);
      expect(result.steps_completed).toBe(0);
      expect(result.errors.length).toBeGreaterThan(0);
    });
  });

  describe("System Validation", () => {
    it("should validate system integrity", async () => {
      const validation = await upgrade.validateSystemIntegrity();
      
      expect(validation).toBeDefined();
      expect(validation.valid).toBe(true);
      expect(validation.issues).toHaveLength(0);
      expect(validation.recommendations).toBeDefined();
    });

    it("should detect system issues", async () => {
      // Disable quantum resistance to simulate issues
      upgrade.updateConfig({ enable_quantum_resistance: false });
      
      const validation = await upgrade.validateSystemIntegrity();
      
      expect(validation).toBeDefined();
      expect(validation.valid).toBe(false);
      expect(validation.issues.length).toBeGreaterThan(0);
    });
  });

  describe("Performance Monitoring", () => {
    it("should monitor performance", () => {
      const operation = "test_operation";
      const duration = 100;
      
      upgrade.monitorPerformance(operation, duration);
      
      const stats = upgrade.getPerformanceStats();
      expect(stats.has(operation)).toBe(true);
      
      const operationStats = stats.get(operation);
      expect(operationStats).toBeDefined();
      expect(operationStats!.count).toBe(1);
      expect(operationStats!.average).toBe(duration);
      expect(operationStats!.min).toBe(duration);
      expect(operationStats!.max).toBe(duration);
    });

    it("should track multiple performance measurements", () => {
      const operation = "multi_test_operation";
      const durations = [50, 100, 150, 200];
      
      for (const duration of durations) {
        upgrade.monitorPerformance(operation, duration);
      }
      
      const stats = upgrade.getPerformanceStats();
      const operationStats = stats.get(operation);
      
      expect(operationStats!.count).toBe(4);
      expect(operationStats!.average).toBe(125);
      expect(operationStats!.min).toBe(50);
      expect(operationStats!.max).toBe(200);
    });

    it("should limit performance history", () => {
      const operation = "limit_test_operation";
      
      // Add more than 100 measurements
      for (let i = 0; i < 150; i++) {
        upgrade.monitorPerformance(operation, i);
      }
      
      const stats = upgrade.getPerformanceStats();
      const operationStats = stats.get(operation);
      
      expect(operationStats!.count).toBe(100); // Should be limited to 100
    });
  });

  describe("System Status", () => {
    it("should provide system status", () => {
      const status = upgrade.getSystemStatus();
      
      expect(status).toBeDefined();
      expect(status.quantum_resistant_enabled).toBe(true);
      expect(status.hybrid_mode).toBe(false);
      expect(status.migration_threshold).toBe(0.95);
      expect(status.system_health).toBe("HEALTHY");
      expect(status.performance_metrics).toBeDefined();
    });

    it("should reflect configuration changes in status", () => {
      upgrade.updateConfig({ 
        enable_quantum_resistance: false,
        hybrid_mode: true,
        migration_threshold: 0.9
      });
      
      const status = upgrade.getSystemStatus();
      
      expect(status.quantum_resistant_enabled).toBe(false);
      expect(status.hybrid_mode).toBe(true);
      expect(status.migration_threshold).toBe(0.9);
    });
  });

  describe("Global Functions", () => {
    it("should work with global upgrade instance", () => {
      const globalUpgrade = getQuantumResistantUpgrade();
      expect(globalUpgrade).toBeDefined();
      expect(globalUpgrade).toBeInstanceOf(QuantumResistantUpgrade);
    });

    it("should work with convenience functions", async () => {
      const currentSystem = "classical_crypto";
      const targetSystem = "quantum_resistant_crypto";
      const requirements = {
        performance_target: 0.9,
        security_level: 0.95,
        compatibility_required: true
      };
      
      const plan = await createMigrationPlan(currentSystem, targetSystem, requirements);
      expect(plan).toBeDefined();
      
      const result = await executeQuantumResistantMigration(plan);
      expect(result).toBeDefined();
      expect(result.success).toBe(true);
    });

    it("should upgrade to quantum-resistant system", async () => {
      const upgradedSystem = await upgradeToQuantumResistant({
        enable_quantum_resistance: true,
        hybrid_mode: false
      });
      
      expect(upgradedSystem).toBeDefined();
      expect(upgradedSystem).toBeInstanceOf(QuantumResistantUpgrade);
    });
  });

  describe("Error Handling", () => {
    it("should handle invalid inputs gracefully", async () => {
      const input = null;
      const domain = "";
      
      // Should not throw error
      const result = await upgrade.hybridHash(input, domain);
      expect(result).toBeDefined();
    });

    it("should handle migration errors gracefully", async () => {
      const invalidPlan: MigrationPlan = {
        current_system: "",
        target_system: "",
        migration_steps: [],
        estimated_time_ms: 0,
        risk_assessment: "",
        rollback_plan: []
      };
      
      const result = await upgrade.executeMigration(invalidPlan);
      
      expect(result.success).toBe(false);
      expect(result.errors.length).toBeGreaterThan(0);
    });
  });
});

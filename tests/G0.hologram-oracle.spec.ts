import { describe, it, expect } from "vitest";
import path from "node:path";
import { HologramOracle } from "../src/validator/HologramOracle";

const goodModule = path.resolve("data/modules/example-good.json");
const badModule = path.resolve("data/modules/example-bad.json");
const blueprint = path.resolve("modules/atlas-12288/blueprint/blueprint.json");

describe("G0: Hologram Oracle Validation", () => {
  const validator = new HologramOracle();

  describe("Module Oracle Validation", () => {
    it("validates good module with high oracle score", () => {
      const result = validator.validateModule(goodModule);
      
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThanOrEqual(0.95);
      expect(result.violations).toHaveLength(0);
      expect(result.holographic_fingerprint).toBeTruthy();
    });

    it("identifies oracle violations in bad module", () => {
      const result = validator.validateModule(badModule);
      
      expect(result.ok).toBe(false);
      expect(result.oracle_score).toBeLessThan(0.95);
      expect(result.violations.length).toBeGreaterThan(0);
      
      // Should have holographic correspondence violation
      const holographicViolations = result.violations.filter(
        v => v.type === 'holographic_correspondence'
      );
      expect(holographicViolations.length).toBeGreaterThan(0);
    });

    it("validates holographic correspondence invariant", () => {
      const result = validator.validateModule(goodModule);
      
      // Good module should have holographic_correspondence
      expect(result.violations).not.toContainEqual(
        expect.objectContaining({
          type: 'holographic_correspondence',
          severity: 'critical'
        })
      );
    });

    it("validates resonance classification invariant", () => {
      const result = validator.validateModule(goodModule);
      
      // Should not have critical resonance violations
      const resonanceViolations = result.violations.filter(
        v => v.type === 'resonance_mismatch' && v.severity === 'critical'
      );
      expect(resonanceViolations).toHaveLength(0);
    });

    it("validates cycle conservation invariant", () => {
      const result = validator.validateModule(goodModule);
      
      // Should not have critical cycle violations
      const cycleViolations = result.violations.filter(
        v => v.type === 'cycle_violation' && v.severity === 'critical'
      );
      expect(cycleViolations).toHaveLength(0);
    });

    it("validates page conservation invariant", () => {
      const result = validator.validateModule(goodModule);
      
      // Should not have critical page conservation violations
      const pageViolations = result.violations.filter(
        v => v.type === 'page_conservation' && v.severity === 'critical'
      );
      expect(pageViolations).toHaveLength(0);
    });
  });

  describe("Blueprint Coherence Validation", () => {
    it("validates blueprint oracle", () => {
      const result = validator.validateBlueprint(blueprint);
      
      expect(result.ok).toBe(true);
      expect(result.oracle_score).toBeGreaterThanOrEqual(0.95);
      expect(result.holographic_fingerprint).toBeTruthy();
    });

    it("validates blueprint self-reference", () => {
      const result = validator.validateBlueprint(blueprint);
      
      // Should not have critical self-reference violations
      const selfViolations = result.violations.filter(
        v => v.type === 'holographic_correspondence' && 
             v.message.includes('self.fingerprint')
      );
      expect(selfViolations).toHaveLength(0);
    });
  });

  describe("Coherence Scoring", () => {
    it("calculates oracle scores correctly", () => {
      const goodResult = validator.validateModule(goodModule);
      const badResult = validator.validateModule(badModule);
      
      expect(goodResult.oracle_score).toBeGreaterThan(badResult.oracle_score);
      expect(goodResult.oracle_score).toBeGreaterThanOrEqual(0.95);
      expect(badResult.oracle_score).toBeLessThan(0.95);
    });

    it("generates consistent holographic fingerprints", () => {
      const result1 = validator.validateModule(goodModule);
      const result2 = validator.validateModule(goodModule);
      
      expect(result1.holographic_fingerprint).toBe(result2.holographic_fingerprint);
    });
  });

  describe("Violation Classification", () => {
    it("classifies violations by severity", () => {
      const result = validator.validateModule(badModule);
      
      const criticalViolations = result.violations.filter(v => v.severity === 'critical');
      const warningViolations = result.violations.filter(v => v.severity === 'warning');
      const infoViolations = result.violations.filter(v => v.severity === 'info');
      
      expect(criticalViolations.length + warningViolations.length + infoViolations.length)
        .toBe(result.violations.length);
    });

    it("provides detailed violation information", () => {
      const result = validator.validateModule(badModule);
      
      if (result.violations.length > 0) {
        const violation = result.violations[0];
        expect(violation.type).toBeTruthy();
        expect(violation.severity).toBeTruthy();
        expect(violation.message).toBeTruthy();
      }
    });
  });

  describe("Integration with Hologram Generator Mini", () => {
    it("validates against reference implementation", () => {
      const validator = new HologramOracle("hologram_generator_mini_reference_fingerprint_v1");
      const result = validator.validateModule(goodModule);
      
      expect(result.holographic_fingerprint).toBeTruthy();
      // The fingerprint should be consistent with reference
      expect(typeof result.holographic_fingerprint).toBe('string');
      expect(result.holographic_fingerprint.length).toBe(64); // SHA256 hex length
    });

    it("maintains oracle with reference standards", () => {
      const result = validator.validateModule(goodModule);
      
      // All critical violations should be resolved for reference compliance
      const criticalViolations = result.violations.filter(v => v.severity === 'critical');
      expect(criticalViolations).toHaveLength(0);
    });
  });
});

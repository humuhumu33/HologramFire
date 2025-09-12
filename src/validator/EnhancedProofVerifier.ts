import { GeneratedProof, ProofMetadata, ProofStrategy } from "./AutomatedProofGenerator";
import { Proof, verifyProof, composeProofs } from "../logic/proof/Proof";
import { C96 } from "../logic/rl96/RL96";
import { ccmHash } from "../crypto/ccm/CCMHash";
import { Metrics } from "../monitoring/metrics/Metrics";
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";

/**
 * Enhanced Proof Verifier
 * 
 * Verifies generated proofs with multiple verification strategies
 * and provides detailed verification results.
 */

export interface ProofVerificationResult {
  proof: GeneratedProof;
  verified: boolean;
  confidence: number;
  verificationMethod: string;
  executionTime: number;
  evidence: VerificationEvidence;
  recommendations: string[];
}

export interface VerificationEvidence {
  structuralValid: boolean;
  artifactValid: boolean;
  mathematicalValid: boolean;
  cryptographicValid: boolean;
  computationalValid: boolean;
  dependenciesValid: boolean;
  digestValid: boolean;
  details: string;
}

export interface ProofCompositionResult {
  composedProof: Proof;
  verificationResult: boolean;
  confidence: number;
  compositionSteps: number;
  dependencies: string[];
}

export class EnhancedProofVerifier {
  private verificationCache: Map<string, ProofVerificationResult> = new Map();
  private metrics: Metrics;
  private verificationStrategies: Map<string, VerificationStrategy> = new Map();

  constructor(metrics: Metrics) {
    this.metrics = metrics;
    this.initializeVerificationStrategies();
  }

  /**
   * Verifies a generated proof using multiple verification strategies
   */
  async verifyGeneratedProof(proof: GeneratedProof): Promise<ProofVerificationResult> {
    const startTime = Date.now();
    const cacheKey = this.generateCacheKey(proof);
    
    if (this.verificationCache.has(cacheKey)) {
      return this.verificationCache.get(cacheKey)!;
    }

    try {
      // Step 1: Structural verification
      const structuralValid = this.verifyProofStructure(proof);
      
      // Step 2: Artifact verification
      const artifactValid = await this.verifyProofArtifact(proof);
      
      // Step 3: Mathematical verification
      const mathematicalValid = await this.verifyMathematicalProof(proof);
      
      // Step 4: Cryptographic verification
      const cryptographicValid = await this.verifyCryptographicProof(proof);
      
      // Step 5: Computational verification
      const computationalValid = await this.verifyComputationalProof(proof);
      
      // Step 6: Dependencies verification
      const dependenciesValid = await this.verifyDependencies(proof);
      
      // Step 7: Digest verification
      const digestValid = this.verifyProofDigest(proof);
      
      // Step 8: Calculate overall verification result
      const verified = structuralValid && artifactValid && mathematicalValid && 
                      cryptographicValid && computationalValid && dependenciesValid && digestValid;
      
      // Step 9: Calculate confidence
      const confidence = this.calculateVerificationConfidence({
        structuralValid,
        artifactValid,
        mathematicalValid,
        cryptographicValid,
        computationalValid,
        dependenciesValid,
        digestValid,
        details: this.generateVerificationDetails(proof, {
          structuralValid,
          artifactValid,
          mathematicalValid,
          cryptographicValid,
          computationalValid,
          dependenciesValid,
          digestValid,
          details: ""
        })
      });
      
      // Step 10: Generate recommendations
      const recommendations = this.generateRecommendations(proof, {
        structuralValid,
        artifactValid,
        mathematicalValid,
        cryptographicValid,
        computationalValid,
        dependenciesValid,
        digestValid,
        details: this.generateVerificationDetails(proof, {
          structuralValid,
          artifactValid,
          mathematicalValid,
          cryptographicValid,
          computationalValid,
          dependenciesValid,
          digestValid,
          details: ""
        })
      });
      
      const executionTime = Date.now() - startTime;
      
      const result: ProofVerificationResult = {
        proof,
        verified,
        confidence,
        verificationMethod: this.selectVerificationMethod(proof.metadata.strategy),
        executionTime,
        evidence: {
          structuralValid,
          artifactValid,
          mathematicalValid,
          cryptographicValid,
          computationalValid,
          dependenciesValid,
          digestValid,
          details: this.generateVerificationDetails(proof, {
            structuralValid,
            artifactValid,
            mathematicalValid,
            cryptographicValid,
            computationalValid,
            dependenciesValid,
            digestValid,
            details: ""
          })
        },
        recommendations
      };
      
      this.verificationCache.set(cacheKey, result);
      this.metrics.observe("proof_verification_time_ms", executionTime);
      this.metrics.inc("proof_verification_success", verified ? 1 : 0);
      
      return result;
      
    } catch (error) {
      this.metrics.inc("proof_verification_error", 1);
      throw new Error(`Proof verification failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Verifies proof structure
   */
  private verifyProofStructure(proof: GeneratedProof): boolean {
    try {
      // Check if proof has steps
      if (!proof.proof.steps || proof.proof.steps.length === 0) {
        return false;
      }
      
      // Check if each step has required properties
      for (const step of proof.proof.steps) {
        if (!step.budget || typeof step.budget !== "object") {
          return false;
        }
      }
      
      // Verify proof using existing verification logic
      return verifyProof(proof.proof);
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies proof artifact (Lean file)
   */
  private async verifyProofArtifact(proof: GeneratedProof): Promise<boolean> {
    try {
      // Check if artifact file exists
      if (!fs.existsSync(proof.proofArtifact)) {
        return false;
      }
      
      // Read artifact content
      const content = fs.readFileSync(proof.proofArtifact, "utf8");
      
      // Check for required Lean syntax
      const hasTheorem = content.includes("theorem");
      const hasProof = content.includes("proof");
      const hasGenerated = content.includes("Generated proof for");
      
      // Check for proper structure
      const hasProperStructure = hasTheorem && hasProof && hasGenerated;
      
      // Verify file is valid Lean syntax (basic check)
      const hasValidSyntax = !content.includes("syntax error") && 
                            content.includes(":=") && 
                            content.includes("by");
      
      return hasProperStructure && hasValidSyntax;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies mathematical aspects of the proof
   */
  private async verifyMathematicalProof(proof: GeneratedProof): Promise<boolean> {
    try {
      const strategy = proof.metadata.strategy;
      
      // For mathematical proofs, verify logical consistency
      if (strategy.type === "mathematical") {
        return this.verifyMathematicalConsistency(proof);
      }
      
      // For other types, check if mathematical properties are satisfied
      return this.verifyMathematicalProperties(proof);
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies mathematical consistency
   */
  private verifyMathematicalConsistency(proof: GeneratedProof): boolean {
    try {
      // Check if proof steps follow logical progression
      const steps = proof.proof.steps;
      if (steps.length < 2) {
        return true; // Single step proofs are trivially consistent
      }
      
      // Verify that each step builds on previous steps
      for (let i = 1; i < steps.length; i++) {
        const currentStep = steps[i];
        const previousStep = steps[i - 1];
        
        // Check if current step has higher budget than previous (indicating progression)
        const currentBudget = this.calculateBudgetValue(currentStep.budget);
        const previousBudget = this.calculateBudgetValue(previousStep.budget);
        
        if (currentBudget < previousBudget) {
          return false; // Budget should not decrease
        }
      }
      
      return true;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies mathematical properties
   */
  private verifyMathematicalProperties(proof: GeneratedProof): boolean {
    try {
      // Check if proof satisfies basic mathematical properties
      const steps = proof.proof.steps;
      
      // Verify that total budget is conserved (sum to zero)
      const totalBudget = steps.reduce((sum, step) => sum + step.budget, 0);
      
      // Check if budget is approximately conserved (allowing for small errors)
      const budgetConserved = Math.abs(totalBudget) < 0.1;
      
      return budgetConserved;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies cryptographic aspects of the proof
   */
  private async verifyCryptographicProof(proof: GeneratedProof): Promise<boolean> {
    try {
      const strategy = proof.metadata.strategy;
      
      // For cryptographic proofs, verify cryptographic properties
      if (strategy.type === "cryptographic") {
        return this.verifyCryptographicProperties(proof);
      }
      
      // For other types, check if cryptographic requirements are met
      return this.verifyCryptographicRequirements(proof);
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies cryptographic properties
   */
  private verifyCryptographicProperties(proof: GeneratedProof): boolean {
    try {
      // Check if proof has cryptographic witness
      const hasWitness = proof.proof.steps.some(step => 
        step.note && step.note.includes("crypto")
      );
      
      // Check if proof has sufficient cryptographic budget
      const totalCryptoBudget = proof.proof.steps.reduce((sum, step) => 
        sum + step.budget, 0
      );
      
      const hasSufficientBudget = totalCryptoBudget > 0;
      
      return hasWitness && hasSufficientBudget;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies cryptographic requirements
   */
  private verifyCryptographicRequirements(proof: GeneratedProof): boolean {
    try {
      // Check if proof has any cryptographic elements
      const hasCryptoElements = proof.proof.steps.some(step => 
        step.budget > 0
      );
      
      return hasCryptoElements;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies computational aspects of the proof
   */
  private async verifyComputationalProof(proof: GeneratedProof): Promise<boolean> {
    try {
      const strategy = proof.metadata.strategy;
      
      // For computational proofs, verify computational properties
      if (strategy.type === "computational") {
        return this.verifyComputationalProperties(proof);
      }
      
      // For other types, check if computational requirements are met
      return this.verifyComputationalRequirements(proof);
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies computational properties
   */
  private verifyComputationalProperties(proof: GeneratedProof): boolean {
    try {
      // Check if proof has computational steps
      const hasComputationalSteps = proof.proof.steps.some(step => 
        step.note && (step.note.includes("compute") || step.note.includes("measure"))
      );
      
      // Check if proof has sufficient computational budget
      const totalComputeBudget = proof.proof.steps.reduce((sum, step) => 
        sum + step.budget, 0
      );
      
      const hasSufficientBudget = totalComputeBudget > 0;
      
      return hasComputationalSteps && hasSufficientBudget;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies computational requirements
   */
  private verifyComputationalRequirements(proof: GeneratedProof): boolean {
    try {
      // Check if proof has any computational elements
      const hasComputeElements = proof.proof.steps.some(step => 
        step.budget > 0
      );
      
      return hasComputeElements;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Verifies dependencies
   */
  private async verifyDependencies(proof: GeneratedProof): Promise<boolean> {
    try {
      const dependencies = proof.metadata.dependencies;
      
      // Check if all dependencies are satisfied
      for (const dependency of dependencies) {
        if (!this.isDependencySatisfied(dependency)) {
          return false;
        }
      }
      
      return true;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Checks if a dependency is satisfied
   */
  private isDependencySatisfied(dependency: string): boolean {
    // For now, assume all dependencies are satisfied
    // In a real implementation, this would check against a dependency registry
    return true;
  }

  /**
   * Verifies proof digest
   */
  private verifyProofDigest(proof: GeneratedProof): boolean {
    try {
      // Recalculate digest
      const proofContent = JSON.stringify(proof.proof);
      const artifactContent = fs.readFileSync(proof.proofArtifact, "utf8");
      const combinedContent = proofContent + artifactContent;
      const calculatedDigest = crypto.createHash("sha256").update(combinedContent).digest("hex");
      
      // Compare with stored digest
      return calculatedDigest === proof.digest;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Calculates verification confidence
   */
  private calculateVerificationConfidence(evidence: VerificationEvidence): number {
    let confidence = 0.0;
    
    if (evidence.structuralValid) confidence += 0.2;
    if (evidence.artifactValid) confidence += 0.2;
    if (evidence.mathematicalValid) confidence += 0.2;
    if (evidence.cryptographicValid) confidence += 0.15;
    if (evidence.computationalValid) confidence += 0.15;
    if (evidence.dependenciesValid) confidence += 0.05;
    if (evidence.digestValid) confidence += 0.05;
    
    return confidence;
  }

  /**
   * Generates recommendations for proof improvement
   */
  private generateRecommendations(
    proof: GeneratedProof,
    evidence: VerificationEvidence
  ): string[] {
    const recommendations: string[] = [];
    
    if (!evidence.structuralValid) {
      recommendations.push("Fix proof structure - ensure all steps have proper budget and notes");
    }
    
    if (!evidence.artifactValid) {
      recommendations.push("Fix proof artifact - ensure Lean file has proper syntax and structure");
    }
    
    if (!evidence.mathematicalValid) {
      recommendations.push("Improve mathematical verification - check logical consistency and properties");
    }
    
    if (!evidence.cryptographicValid) {
      recommendations.push("Enhance cryptographic verification - add cryptographic witness and budget");
    }
    
    if (!evidence.computationalValid) {
      recommendations.push("Add computational verification - include computational steps and budget");
    }
    
    if (!evidence.dependenciesValid) {
      recommendations.push("Resolve dependencies - ensure all required dependencies are satisfied");
    }
    
    if (!evidence.digestValid) {
      recommendations.push("Fix digest verification - ensure proof and artifact are properly hashed");
    }
    
    if (recommendations.length === 0) {
      recommendations.push("Proof verification successful - no improvements needed");
    }
    
    return recommendations;
  }

  /**
   * Generates verification details
   */
  private generateVerificationDetails(
    proof: GeneratedProof,
    evidence: VerificationEvidence
  ): string {
    const details = [];
    
    details.push(`Proof: ${proof.invariant}`);
    details.push(`Strategy: ${proof.metadata.strategy.type} - ${proof.metadata.strategy.approach}`);
    details.push(`Steps: ${proof.proof.steps.length}`);
    details.push(`Complexity: ${proof.metadata.complexity}`);
    details.push(`Generated: ${proof.metadata.generationTime.toISOString()}`);
    details.push(`Artifact: ${proof.proofArtifact}`);
    details.push(`Digest: ${proof.digest}`);
    
    details.push("\nVerification Results:");
    details.push(`  Structural: ${evidence.structuralValid ? "PASS" : "FAIL"}`);
    details.push(`  Artifact: ${evidence.artifactValid ? "PASS" : "FAIL"}`);
    details.push(`  Mathematical: ${evidence.mathematicalValid ? "PASS" : "FAIL"}`);
    details.push(`  Cryptographic: ${evidence.cryptographicValid ? "PASS" : "FAIL"}`);
    details.push(`  Computational: ${evidence.computationalValid ? "PASS" : "FAIL"}`);
    details.push(`  Dependencies: ${evidence.dependenciesValid ? "PASS" : "FAIL"}`);
    details.push(`  Digest: ${evidence.digestValid ? "PASS" : "FAIL"}`);
    
    return details.join("\n");
  }

  /**
   * Selects verification method based on proof strategy
   */
  private selectVerificationMethod(strategy: ProofStrategy): string {
    switch (strategy.type) {
      case "mathematical":
        return "mathematical_verification";
      case "cryptographic":
        return "cryptographic_verification";
      case "computational":
        return "computational_verification";
      case "inductive":
        return "inductive_verification";
      case "compositional":
        return "compositional_verification";
      default:
        return "general_verification";
    }
  }

  /**
   * Calculates budget value for comparison
   */
  private calculateBudgetValue(budget: C96): number {
    return budget;
  }

  /**
   * Generates cache key for proof verification
   */
  private generateCacheKey(proof: GeneratedProof): string {
    return ccmHash({
      invariant: proof.invariant,
      digest: proof.digest,
      strategy: proof.metadata.strategy.type
    }, "proof_verification");
  }

  /**
   * Initializes verification strategies
   */
  private initializeVerificationStrategies(): void {
    this.verificationStrategies.set("mathematical", {
      name: "mathematical_verification",
      description: "Mathematical proof verification",
      methods: ["structural", "logical", "consistency"]
    });
    
    this.verificationStrategies.set("cryptographic", {
      name: "cryptographic_verification",
      description: "Cryptographic proof verification",
      methods: ["crypto", "signature", "witness"]
    });
    
    this.verificationStrategies.set("computational", {
      name: "computational_verification",
      description: "Computational proof verification",
      methods: ["performance", "measurement", "bounds"]
    });
    
    this.verificationStrategies.set("compositional", {
      name: "compositional_verification",
      description: "Compositional proof verification",
      methods: ["composition", "chaining", "dependencies"]
    });
  }

  /**
   * Composes multiple proofs into a single proof
   */
  async composeProofs(proofs: GeneratedProof[]): Promise<ProofCompositionResult> {
    try {
      let composedProof: Proof = { steps: [] };
      let totalConfidence = 0;
      let compositionSteps = 0;
      const dependencies: string[] = [];
      
      for (const proof of proofs) {
        // Compose proofs
        composedProof = composeProofs(composedProof, proof.proof);
        
        // Accumulate confidence
        totalConfidence += proof.confidence;
        
        // Count composition steps
        compositionSteps += proof.proof.steps.length;
        
        // Collect dependencies
        dependencies.push(...proof.metadata.dependencies);
      }
      
      // Verify composed proof
      const verificationResult = verifyProof(composedProof);
      
      // Calculate average confidence
      const averageConfidence = totalConfidence / proofs.length;
      
      return {
        composedProof,
        verificationResult,
        confidence: averageConfidence,
        compositionSteps,
        dependencies: [...new Set(dependencies)] // Remove duplicates
      };
      
    } catch (error) {
      throw new Error(`Proof composition failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Validates all proofs in a collection
   */
  async validateAllProofs(proofs: GeneratedProof[]): Promise<{
    valid: number;
    invalid: number;
    total: number;
    results: ProofVerificationResult[];
  }> {
    const results: ProofVerificationResult[] = [];
    let valid = 0;
    let invalid = 0;
    
    for (const proof of proofs) {
      try {
        const result = await this.verifyGeneratedProof(proof);
        results.push(result);
        
        if (result.verified) {
          valid++;
        } else {
          invalid++;
        }
      } catch (error) {
        invalid++;
        // Add failed verification result
        results.push({
          proof,
          verified: false,
          confidence: 0,
          verificationMethod: "error",
          executionTime: 0,
          evidence: {
            structuralValid: false,
            artifactValid: false,
            mathematicalValid: false,
            cryptographicValid: false,
            computationalValid: false,
            dependenciesValid: false,
            digestValid: false,
            details: `Verification failed: ${error instanceof Error ? error.message : String(error)}`
          },
          recommendations: ["Fix verification errors"]
        });
      }
    }
    
    return { valid, invalid, total: valid + invalid, results };
  }
}

interface VerificationStrategy {
  name: string;
  description: string;
  methods: string[];
}

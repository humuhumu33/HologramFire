import { AutomatedProofGenerator, GeneratedProof } from "./AutomatedProofGenerator";
import { EnhancedProofVerifier, ProofVerificationResult } from "./EnhancedProofVerifier";
import { InvariantAnalyzer } from "./InvariantAnalyzer";
import { InvariantAnalysis } from "./AutomatedProofGenerator";
import { ProofComposer, ProofChain } from "./ProofComposer";
import { VerificationContext } from "./InvariantVerifier";
import { Metrics } from "../monitoring/metrics/Metrics";
import { ccmHash } from "../crypto/ccm/CCMHash";

/**
 * Automated Proof System
 * 
 * Main integration module that coordinates all components
 * for automated proof generation, verification, and management.
 */

export interface ProofSystemConfig {
  enableCaching: boolean;
  enableOptimization: boolean;
  enableComposition: boolean;
  maxProofSteps: number;
  confidenceThreshold: number;
  verificationTimeout: number;
}

export interface ProofSystemStats {
  totalProofs: number;
  successfulProofs: number;
  failedProofs: number;
  averageConfidence: number;
  averageGenerationTime: number;
  averageVerificationTime: number;
  proofChains: number;
  totalSteps: number;
}

export interface ProofSystemResult {
  success: boolean;
  proof?: GeneratedProof;
  verification?: ProofVerificationResult;
  analysis?: InvariantAnalysis;
  error?: string;
  executionTime: number;
}

export class AutomatedProofSystem {
  private proofGenerator: AutomatedProofGenerator;
  private proofVerifier: EnhancedProofVerifier;
  private invariantAnalyzer: InvariantAnalyzer;
  private proofComposer: ProofComposer;
  private metrics: Metrics;
  private config: ProofSystemConfig;
  private stats: ProofSystemStats;

  constructor(config: Partial<ProofSystemConfig> = {}) {
    this.config = {
      enableCaching: true,
      enableOptimization: true,
      enableComposition: true,
      maxProofSteps: 100,
      confidenceThreshold: 0.7,
      verificationTimeout: 30000,
      ...config
    };

    this.metrics = new Metrics();
    this.proofGenerator = new AutomatedProofGenerator(this.metrics);
    this.proofVerifier = new EnhancedProofVerifier(this.metrics);
    this.invariantAnalyzer = new InvariantAnalyzer(this.metrics);
    this.proofComposer = new ProofComposer(this.metrics);

    this.stats = {
      totalProofs: 0,
      successfulProofs: 0,
      failedProofs: 0,
      averageConfidence: 0,
      averageGenerationTime: 0,
      averageVerificationTime: 0,
      proofChains: 0,
      totalSteps: 0
    };
  }

  /**
   * Generates and verifies proof for an invariant
   */
  async generateAndVerifyProof(
    invariant: string,
    context: VerificationContext
  ): Promise<ProofSystemResult> {
    const startTime = Date.now();
    
    try {
      // Step 1: Analyze invariant
      const analysis = await this.invariantAnalyzer.analyzeInvariant(invariant, context);
      
      // Step 2: Generate proof
      const proof = await this.proofGenerator.generateProofForInvariant(invariant, context);
      
      // Step 3: Verify proof
      const verification = await this.proofVerifier.verifyGeneratedProof(proof);
      
      // Step 4: Update stats
      this.updateStats(proof, verification, Date.now() - startTime);
      
      return {
        success: true,
        proof,
        verification,
        analysis,
        executionTime: Date.now() - startTime
      };
      
    } catch (error) {
      this.stats.failedProofs++;
      this.stats.totalProofs++;
      
      return {
        success: false,
        error: error instanceof Error ? error.message : String(error),
        executionTime: Date.now() - startTime
      };
    }
  }

  /**
   * Generates proofs for multiple invariants
   */
  async generateProofsForInvariants(
    invariants: string[],
    context: VerificationContext
  ): Promise<ProofSystemResult[]> {
    const results: ProofSystemResult[] = [];
    
    for (const invariant of invariants) {
      const result = await this.generateAndVerifyProof(invariant, context);
      results.push(result);
    }
    
    return results;
  }

  /**
   * Creates a proof chain from multiple proofs
   */
  async createProofChain(
    name: string,
    invariants: string[],
    context: VerificationContext,
    strategy: "sequential" | "parallel" | "hierarchical" | "conditional" = "sequential"
  ): Promise<ProofChain | null> {
    try {
      // Generate proofs for all invariants
      const results = await this.generateProofsForInvariants(invariants, context);
      
      // Filter successful proofs
      const successfulProofs = results
        .filter(result => result.success && result.proof)
        .map(result => result.proof!);
      
      if (successfulProofs.length === 0) {
        throw new Error("No successful proofs to compose");
      }
      
      // Create composition strategy
      const compositionStrategy = {
        type: strategy,
        approach: `${strategy}_composition`,
        compositionRules: [],
        optimizationLevel: this.config.enableOptimization ? "advanced" as const : "basic" as const
      };
      
      // Compose proof chain
      const proofChain = await this.proofComposer.composeProofChain(
        name,
        successfulProofs,
        compositionStrategy
      );
      
      this.stats.proofChains++;
      
      return proofChain;
      
    } catch (error) {
      console.error(`Failed to create proof chain: ${error instanceof Error ? error.message : String(error)}`);
      return null;
    }
  }

  /**
   * Validates all generated proofs
   */
  async validateAllProofs(): Promise<{
    valid: number;
    invalid: number;
    total: number;
    results: ProofVerificationResult[];
  }> {
    const generatedProofs = this.proofGenerator.listGeneratedProofs();
    return this.proofVerifier.validateAllProofs(generatedProofs);
  }

  /**
   * Gets system statistics
   */
  getStats(): ProofSystemStats {
    return { ...this.stats };
  }

  /**
   * Resets system statistics
   */
  resetStats(): void {
    this.stats = {
      totalProofs: 0,
      successfulProofs: 0,
      failedProofs: 0,
      averageConfidence: 0,
      averageGenerationTime: 0,
      averageVerificationTime: 0,
      proofChains: 0,
      totalSteps: 0
    };
  }

  /**
   * Gets configuration
   */
  getConfig(): ProofSystemConfig {
    return { ...this.config };
  }

  /**
   * Updates configuration
   */
  updateConfig(newConfig: Partial<ProofSystemConfig>): void {
    this.config = { ...this.config, ...newConfig };
  }

  /**
   * Gets all generated proofs
   */
  getAllProofs(): GeneratedProof[] {
    return this.proofGenerator.listGeneratedProofs();
  }

  /**
   * Gets all proof chains
   */
  getAllProofChains(): ProofChain[] {
    return this.proofComposer.listProofChains();
  }

  /**
   * Gets proof by invariant name
   */
  getProofByInvariant(invariant: string): GeneratedProof | undefined {
    return this.proofGenerator.getGeneratedProof(invariant);
  }

  /**
   * Gets proof chain by ID
   */
  getProofChainById(id: string): ProofChain | undefined {
    return this.proofComposer.getProofChain(id);
  }

  /**
   * Analyzes an invariant without generating proof
   */
  async analyzeInvariant(
    invariant: string,
    context: VerificationContext
  ): Promise<InvariantAnalysis> {
    return this.invariantAnalyzer.analyzeInvariant(invariant, context);
  }

  /**
   * Verifies an existing proof
   */
  async verifyProof(proof: GeneratedProof): Promise<ProofVerificationResult> {
    return this.proofVerifier.verifyGeneratedProof(proof);
  }

  /**
   * Exports all proofs to a directory
   */
  async exportProofs(outputDir: string): Promise<void> {
    const fs = await import("node:fs");
    const path = await import("node:path");
    
    if (!fs.existsSync(outputDir)) {
      fs.mkdirSync(outputDir, { recursive: true });
    }
    
    // Export individual proofs
    const proofs = this.getAllProofs();
    for (const proof of proofs) {
      const proofFile = path.join(outputDir, `${proof.invariant}_proof.json`);
      fs.writeFileSync(proofFile, JSON.stringify(proof, null, 2));
    }
    
    // Export proof chains
    const chains = this.getAllProofChains();
    for (const chain of chains) {
      const chainFile = path.join(outputDir, `${chain.name}_chain.json`);
      fs.writeFileSync(chainFile, JSON.stringify(chain, null, 2));
    }
    
    // Export statistics
    const statsFile = path.join(outputDir, "proof_system_stats.json");
    fs.writeFileSync(statsFile, JSON.stringify(this.getStats(), null, 2));
  }

  /**
   * Imports proofs from a directory
   */
  async importProofs(inputDir: string): Promise<void> {
    const fs = await import("node:fs");
    const path = await import("node:path");
    
    if (!fs.existsSync(inputDir)) {
      throw new Error(`Input directory not found: ${inputDir}`);
    }
    
    const files = fs.readdirSync(inputDir);
    
    for (const file of files) {
      if (file.endsWith("_proof.json")) {
        const proofFile = path.join(inputDir, file);
        const proofData = JSON.parse(fs.readFileSync(proofFile, "utf8"));
        
        // Add to proof generator cache
        this.proofGenerator["generatedProofs"].set(proofData.invariant, proofData);
      }
    }
  }

  /**
   * Clears all generated proofs and chains
   */
  clearAll(): void {
    this.proofGenerator["generatedProofs"].clear();
    this.proofComposer["proofChains"].clear();
    this.resetStats();
  }

  /**
   * Updates system statistics
   */
  private updateStats(
    proof: GeneratedProof,
    verification: ProofVerificationResult,
    executionTime: number
  ): void {
    this.stats.totalProofs++;
    
    if (proof.verificationResult) {
      this.stats.successfulProofs++;
    } else {
      this.stats.failedProofs++;
    }
    
    // Update averages
    this.stats.averageConfidence = 
      (this.stats.averageConfidence * (this.stats.totalProofs - 1) + proof.confidence) / 
      this.stats.totalProofs;
    
    this.stats.averageGenerationTime = 
      (this.stats.averageGenerationTime * (this.stats.totalProofs - 1) + executionTime) / 
      this.stats.totalProofs;
    
    this.stats.averageVerificationTime = 
      (this.stats.averageVerificationTime * (this.stats.totalProofs - 1) + verification.executionTime) / 
      this.stats.totalProofs;
    
    this.stats.totalSteps += proof.proof.steps.length;
  }

  /**
   * Generates system report
   */
  generateReport(): string {
    const stats = this.getStats();
    const proofs = this.getAllProofs();
    const chains = this.getAllProofChains();
    
    const report = [];
    report.push("=== Automated Proof System Report ===");
    report.push(`Generated: ${new Date().toISOString()}`);
    report.push("");
    
    report.push("Statistics:");
    report.push(`  Total Proofs: ${stats.totalProofs}`);
    report.push(`  Successful: ${stats.successfulProofs}`);
    report.push(`  Failed: ${stats.failedProofs}`);
    report.push(`  Success Rate: ${stats.totalProofs > 0 ? (stats.successfulProofs / stats.totalProofs * 100).toFixed(1) : 0}%`);
    report.push(`  Average Confidence: ${stats.averageConfidence.toFixed(3)}`);
    report.push(`  Average Generation Time: ${stats.averageGenerationTime.toFixed(0)}ms`);
    report.push(`  Average Verification Time: ${stats.averageVerificationTime.toFixed(0)}ms`);
    report.push(`  Proof Chains: ${stats.proofChains}`);
    report.push(`  Total Steps: ${stats.totalSteps}`);
    report.push("");
    
    report.push("Proof Categories:");
    const categories = new Map<string, number>();
    for (const proof of proofs) {
      const category = proof.metadata.strategy.type;
      categories.set(category, (categories.get(category) || 0) + 1);
    }
    for (const [category, count] of categories) {
      report.push(`  ${category}: ${count}`);
    }
    report.push("");
    
    report.push("Proof Chains:");
    for (const chain of chains) {
      report.push(`  ${chain.name}: ${chain.proofs.length} proofs, ${chain.verificationResult ? "PASS" : "FAIL"}`);
    }
    report.push("");
    
    report.push("Configuration:");
    report.push(`  Caching: ${this.config.enableCaching ? "enabled" : "disabled"}`);
    report.push(`  Optimization: ${this.config.enableOptimization ? "enabled" : "disabled"}`);
    report.push(`  Composition: ${this.config.enableComposition ? "enabled" : "disabled"}`);
    report.push(`  Max Proof Steps: ${this.config.maxProofSteps}`);
    report.push(`  Confidence Threshold: ${this.config.confidenceThreshold}`);
    report.push(`  Verification Timeout: ${this.config.verificationTimeout}ms`);
    
    return report.join("\n");
  }
}

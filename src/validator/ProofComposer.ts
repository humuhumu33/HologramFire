import { GeneratedProof, ProofStrategy } from "./AutomatedProofGenerator";
import { Proof, ProofStep, verifyProof, composeProofs } from "../logic/proof/Proof";
import { C96, norm, sum } from "../logic/rl96/RL96";
import { ccmHash } from "../crypto/ccm/CCMHash";
import { Metrics } from "../monitoring/metrics/Metrics";

/**
 * Proof Composition and Chaining System
 * 
 * Composes multiple proofs into complex proof chains
 * and manages proof dependencies and relationships.
 */

export interface ProofChain {
  id: string;
  name: string;
  proofs: GeneratedProof[];
  composedProof: Proof;
  verificationResult: boolean;
  confidence: number;
  dependencies: string[];
  metadata: ProofChainMetadata;
}

export interface ProofChainMetadata {
  creationTime: Date;
  strategy: ProofCompositionStrategy;
  complexity: "low" | "medium" | "high";
  totalSteps: number;
  totalBudget: C96;
  verificationSteps: number;
}

export interface ProofCompositionStrategy {
  type: "sequential" | "parallel" | "hierarchical" | "conditional";
  approach: string;
  compositionRules: CompositionRule[];
  optimizationLevel: "none" | "basic" | "advanced";
}

export interface CompositionRule {
  name: string;
  condition: string;
  action: string;
  priority: number;
}

export interface ProofDependency {
  source: string;
  target: string;
  type: "direct" | "transitive" | "conditional";
  strength: number; // 0-1
  required: boolean;
}

export interface ProofOptimization {
  originalProof: Proof;
  optimizedProof: Proof;
  optimizationType: "budget" | "steps" | "dependencies" | "verification";
  improvement: number; // 0-1
  changes: OptimizationChange[];
}

export interface OptimizationChange {
  type: "merge" | "split" | "reorder" | "simplify";
  description: string;
  before: ProofStep;
  after: ProofStep;
  impact: number;
}

export class ProofComposer {
  private proofChains: Map<string, ProofChain> = new Map();
  private compositionStrategies: Map<string, ProofCompositionStrategy> = new Map();
  private dependencyGraph: Map<string, ProofDependency[]> = new Map();
  private optimizationCache: Map<string, ProofOptimization> = new Map();
  private metrics: Metrics;

  constructor(metrics: Metrics) {
    this.metrics = metrics;
    this.initializeCompositionStrategies();
  }

  /**
   * Composes multiple proofs into a proof chain
   */
  async composeProofChain(
    name: string,
    proofs: GeneratedProof[],
    strategy: ProofCompositionStrategy
  ): Promise<ProofChain> {
    const startTime = Date.now();
    
    try {
      // Step 1: Validate proofs
      this.validateProofs(proofs);
      
      // Step 2: Analyze dependencies
      const dependencies = this.analyzeDependencies(proofs);
      
      // Step 3: Determine composition order
      const orderedProofs = this.determineCompositionOrder(proofs, dependencies);
      
      // Step 4: Compose proofs
      const composedProof = await this.composeProofs(orderedProofs, strategy);
      
      // Step 5: Optimize composition
      const optimizedProof = await this.optimizeComposition(composedProof, strategy);
      
      // Step 6: Verify composition
      const verificationResult = this.verifyComposition(optimizedProof, orderedProofs);
      
      // Step 7: Calculate confidence
      const confidence = this.calculateCompositionConfidence(optimizedProof, orderedProofs);
      
      // Step 8: Create metadata
      const metadata: ProofChainMetadata = {
        creationTime: new Date(),
        strategy,
        complexity: this.assessCompositionComplexity(optimizedProof, orderedProofs),
        totalSteps: optimizedProof.steps.length,
        totalBudget: this.calculateTotalBudget(optimizedProof),
        verificationSteps: this.countVerificationSteps(optimizedProof)
      };
      
      const proofChain: ProofChain = {
        id: this.generateChainId(name),
        name,
        proofs: orderedProofs,
        composedProof: optimizedProof,
        verificationResult,
        confidence,
        dependencies: dependencies.map(dep => dep.target),
        metadata
      };
      
      this.proofChains.set(proofChain.id, proofChain);
      
      const executionTime = Date.now() - startTime;
      this.metrics.observe("proof_composition_time_ms", executionTime);
      this.metrics.inc("proof_composition_success", 1);
      
      return proofChain;
      
    } catch (error) {
      this.metrics.inc("proof_composition_error", 1);
      throw new Error(`Proof composition failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Creates a hierarchical proof chain
   */
  async createHierarchicalChain(
    name: string,
    rootProof: GeneratedProof,
    subProofs: GeneratedProof[]
  ): Promise<ProofChain> {
    const strategy: ProofCompositionStrategy = {
      type: "hierarchical",
      approach: "hierarchical_composition",
      compositionRules: [
        {
          name: "root_first",
          condition: "root_proof_exists",
          action: "compose_root_first",
          priority: 1
        },
        {
          name: "sub_proofs",
          condition: "sub_proofs_exist",
          action: "compose_sub_proofs",
          priority: 2
        }
      ],
      optimizationLevel: "advanced"
    };
    
    return this.composeProofChain(name, [rootProof, ...subProofs], strategy);
  }

  /**
   * Creates a conditional proof chain
   */
  async createConditionalChain(
    name: string,
    conditionProof: GeneratedProof,
    trueProof: GeneratedProof,
    falseProof: GeneratedProof
  ): Promise<ProofChain> {
    const strategy: ProofCompositionStrategy = {
      type: "conditional",
      approach: "conditional_composition",
      compositionRules: [
        {
          name: "condition_check",
          condition: "condition_proof_exists",
          action: "evaluate_condition",
          priority: 1
        },
        {
          name: "branch_selection",
          condition: "condition_result",
          action: "select_branch",
          priority: 2
        }
      ],
      optimizationLevel: "basic"
    };
    
    return this.composeProofChain(name, [conditionProof, trueProof, falseProof], strategy);
  }

  /**
   * Validates proofs for composition
   */
  private validateProofs(proofs: GeneratedProof[]): void {
    if (proofs.length === 0) {
      throw new Error("No proofs provided for composition");
    }
    
    for (const proof of proofs) {
      if (!proof.verificationResult) {
        throw new Error(`Proof ${proof.invariant} is not verified`);
      }
      
      if (proof.confidence < 0.5) {
        throw new Error(`Proof ${proof.invariant} has low confidence: ${proof.confidence}`);
      }
    }
  }

  /**
   * Analyzes dependencies between proofs
   */
  private analyzeDependencies(proofs: GeneratedProof[]): ProofDependency[] {
    const dependencies: ProofDependency[] = [];
    
    for (const proof of proofs) {
      for (const dependency of proof.metadata.dependencies) {
        const targetProof = proofs.find(p => p.invariant === dependency);
        if (targetProof) {
          dependencies.push({
            source: proof.invariant,
            target: dependency,
            type: "direct",
            strength: 1.0,
            required: true
          });
        }
      }
    }
    
    return dependencies;
  }

  /**
   * Determines composition order based on dependencies
   */
  private determineCompositionOrder(
    proofs: GeneratedProof[],
    dependencies: ProofDependency[]
  ): GeneratedProof[] {
    const ordered: GeneratedProof[] = [];
    const visited = new Set<string>();
    const visiting = new Set<string>();
    
    const dfs = (proof: GeneratedProof) => {
      if (visiting.has(proof.invariant)) {
        throw new Error(`Circular dependency detected involving ${proof.invariant}`);
      }
      
      if (visited.has(proof.invariant)) {
        return;
      }
      
      visiting.add(proof.invariant);
      
      // Add dependencies first
      for (const dep of dependencies) {
        if (dep.source === proof.invariant) {
          const depProof = proofs.find(p => p.invariant === dep.target);
          if (depProof) {
            dfs(depProof);
          }
        }
      }
      
      visiting.delete(proof.invariant);
      visited.add(proof.invariant);
      ordered.push(proof);
    };
    
    for (const proof of proofs) {
      dfs(proof);
    }
    
    return ordered;
  }

  /**
   * Composes proofs according to strategy
   */
  private async composeProofs(
    orderedProofs: GeneratedProof[],
    strategy: ProofCompositionStrategy
  ): Promise<Proof> {
    let composedProof: Proof = { steps: [] };
    
    switch (strategy.type) {
      case "sequential":
        composedProof = await this.composeSequentially(orderedProofs);
        break;
      case "parallel":
        composedProof = await this.composeInParallel(orderedProofs);
        break;
      case "hierarchical":
        composedProof = await this.composeHierarchically(orderedProofs);
        break;
      case "conditional":
        composedProof = await this.composeConditionally(orderedProofs);
        break;
      default:
        composedProof = await this.composeSequentially(orderedProofs);
    }
    
    return composedProof;
  }

  /**
   * Composes proofs sequentially
   */
  private async composeSequentially(proofs: GeneratedProof[]): Promise<Proof> {
    let composed: Proof = { steps: [] };
    
    for (const proof of proofs) {
      composed = composeProofs(composed, proof.proof);
    }
    
    return composed;
  }

  /**
   * Composes proofs in parallel
   */
  private async composeInParallel(proofs: GeneratedProof[]): Promise<Proof> {
    const steps: ProofStep[] = [];
    
    for (const proof of proofs) {
      steps.push(...proof.proof.steps);
    }
    
    return { steps };
  }

  /**
   * Composes proofs hierarchically
   */
  private async composeHierarchically(proofs: GeneratedProof[]): Promise<Proof> {
    if (proofs.length === 0) {
      return { steps: [] };
    }
    
    // First proof is root
    const rootProof = proofs[0];
    let composed: Proof = { ...rootProof.proof };
    
    // Add sub-proofs
    for (let i = 1; i < proofs.length; i++) {
      const subProof = proofs[i];
      composed = composeProofs(composed, subProof.proof);
    }
    
    return composed;
  }

  /**
   * Composes proofs conditionally
   */
  private async composeConditionally(proofs: GeneratedProof[]): Promise<Proof> {
    if (proofs.length < 3) {
      throw new Error("Conditional composition requires at least 3 proofs");
    }
    
    const [conditionProof, trueProof, falseProof] = proofs;
    
    // Create conditional step
    const conditionalStep: ProofStep = {
      budget: 1,
      note: `Conditional composition: ${conditionProof.invariant} ? ${trueProof.invariant} : ${falseProof.invariant}`
    };
    
    // Compose based on condition
    let composed: Proof;
    if (conditionProof.verificationResult) {
      composed = composeProofs(conditionProof.proof, trueProof.proof);
    } else {
      composed = composeProofs(conditionProof.proof, falseProof.proof);
    }
    
    // Add conditional step
    composed.steps.push(conditionalStep);
    
    return composed;
  }

  /**
   * Optimizes proof composition
   */
  private async optimizeComposition(
    proof: Proof,
    strategy: ProofCompositionStrategy
  ): Promise<Proof> {
    if (strategy.optimizationLevel === "none") {
      return proof;
    }
    
    const cacheKey = this.generateOptimizationCacheKey(proof, strategy);
    if (this.optimizationCache.has(cacheKey)) {
      return this.optimizationCache.get(cacheKey)!.optimizedProof;
    }
    
    let optimized = proof;
    
    if (strategy.optimizationLevel === "basic") {
      optimized = this.basicOptimization(proof);
    } else if (strategy.optimizationLevel === "advanced") {
      optimized = this.advancedOptimization(proof);
    }
    
    const optimization: ProofOptimization = {
      originalProof: proof,
      optimizedProof: optimized,
      optimizationType: "steps",
      improvement: this.calculateOptimizationImprovement(proof, optimized),
      changes: this.identifyOptimizationChanges(proof, optimized)
    };
    
    this.optimizationCache.set(cacheKey, optimization);
    
    return optimized;
  }

  /**
   * Basic optimization
   */
  private basicOptimization(proof: Proof): Proof {
    // Remove duplicate steps
    const uniqueSteps = proof.steps.filter((step, index, array) => 
      array.findIndex(s => s.note === step.note) === index
    );
    
    return { steps: uniqueSteps };
  }

  /**
   * Advanced optimization
   */
  private advancedOptimization(proof: Proof): Proof {
    // Merge similar steps
    const mergedSteps = this.mergeSimilarSteps(proof.steps);
    
    // Reorder steps for better efficiency
    const reorderedSteps = this.reorderSteps(mergedSteps);
    
    // Simplify complex steps
    const simplifiedSteps = this.simplifySteps(reorderedSteps);
    
    return { steps: simplifiedSteps };
  }

  /**
   * Merges similar proof steps
   */
  private mergeSimilarSteps(steps: ProofStep[]): ProofStep[] {
    const merged: ProofStep[] = [];
    const groups = new Map<string, ProofStep[]>();
    
    // Group similar steps
    for (const step of steps) {
      const key = step.note?.split(":")[0] || "unknown";
      if (!groups.has(key)) {
        groups.set(key, []);
      }
      groups.get(key)!.push(step);
    }
    
    // Merge groups
    for (const [key, group] of groups) {
      if (group.length === 1) {
        merged.push(group[0]);
      } else {
        // Merge multiple steps into one
        const mergedStep: ProofStep = {
          budget: group.reduce((sum, step) => sum + step.budget, 0),
          note: `${key}: merged ${group.length} steps`
        };
        merged.push(mergedStep);
      }
    }
    
    return merged;
  }

  /**
   * Reorders steps for better efficiency
   */
  private reorderSteps(steps: ProofStep[]): ProofStep[] {
    // Sort by budget complexity (lower first)
    return steps.sort((a, b) => {
      const aComplexity = a.budget;
      const bComplexity = b.budget;
      return aComplexity - bComplexity;
    });
  }

  /**
   * Simplifies complex steps
   */
  private simplifySteps(steps: ProofStep[]): ProofStep[] {
    return steps.map(step => {
      // Simplify budget if possible
      const simplifiedBudget = Math.round(step.budget * 100) / 100;
      
      return {
        ...step,
        budget: simplifiedBudget
      };
    });
  }

  /**
   * Verifies composition
   */
  private verifyComposition(proof: Proof, originalProofs: GeneratedProof[]): boolean {
    try {
      // Verify proof structure
      const structureValid = verifyProof(proof);
      
      // Verify all original proofs are included
      const allStepsIncluded = originalProofs.every(originalProof => 
        originalProof.proof.steps.every(originalStep =>
          proof.steps.some(step => step.note === originalStep.note)
        )
      );
      
      return structureValid && allStepsIncluded;
      
    } catch (error) {
      return false;
    }
  }

  /**
   * Calculates composition confidence
   */
  private calculateCompositionConfidence(
    proof: Proof,
    originalProofs: GeneratedProof[]
  ): number {
    // Average confidence of original proofs
    const averageConfidence = originalProofs.reduce((sum, p) => sum + p.confidence, 0) / originalProofs.length;
    
    // Adjust based on composition complexity
    const complexityFactor = Math.max(0.5, 1.0 - (proof.steps.length / 100));
    
    return Math.min(1.0, averageConfidence * complexityFactor);
  }

  /**
   * Assesses composition complexity
   */
  private assessCompositionComplexity(
    proof: Proof,
    originalProofs: GeneratedProof[]
  ): "low" | "medium" | "high" {
    const totalSteps = proof.steps.length;
    const totalProofs = originalProofs.length;
    
    if (totalSteps < 5 && totalProofs < 3) {
      return "low";
    } else if (totalSteps < 15 && totalProofs < 7) {
      return "medium";
    } else {
      return "high";
    }
  }

  /**
   * Calculates total budget
   */
  private calculateTotalBudget(proof: Proof): C96 {
    return proof.steps.reduce((sum, step) => sum + step.budget, 0);
  }

  /**
   * Counts verification steps
   */
  private countVerificationSteps(proof: Proof): number {
    return proof.steps.filter(step => 
      step.note?.includes("verification") || step.note?.includes("verify")
    ).length;
  }

  /**
   * Generates chain ID
   */
  private generateChainId(name: string): string {
    return ccmHash({ name, timestamp: Date.now() }, "proof_chain");
  }

  /**
   * Generates optimization cache key
   */
  private generateOptimizationCacheKey(proof: Proof, strategy: ProofCompositionStrategy): string {
    return ccmHash({
      proof: JSON.stringify(proof),
      strategy: strategy.type,
      optimization: strategy.optimizationLevel
    }, "proof_optimization");
  }

  /**
   * Calculates optimization improvement
   */
  private calculateOptimizationImprovement(original: Proof, optimized: Proof): number {
    const originalSteps = original.steps.length;
    const optimizedSteps = optimized.steps.length;
    
    if (originalSteps === 0) return 0;
    
    return Math.max(0, (originalSteps - optimizedSteps) / originalSteps);
  }

  /**
   * Identifies optimization changes
   */
  private identifyOptimizationChanges(original: Proof, optimized: Proof): OptimizationChange[] {
    const changes: OptimizationChange[] = [];
    
    // Simple heuristic-based change identification
    if (optimized.steps.length < original.steps.length) {
      changes.push({
        type: "merge",
        description: "Merged similar steps",
        before: original.steps[0],
        after: optimized.steps[0],
        impact: 0.5
      });
    }
    
    return changes;
  }

  /**
   * Initializes composition strategies
   */
  private initializeCompositionStrategies(): void {
    this.compositionStrategies.set("sequential", {
      type: "sequential",
      approach: "step_by_step_composition",
      compositionRules: [
        {
          name: "dependency_order",
          condition: "dependencies_exist",
          action: "compose_in_dependency_order",
          priority: 1
        }
      ],
      optimizationLevel: "basic"
    });
    
    this.compositionStrategies.set("parallel", {
      type: "parallel",
      approach: "parallel_composition",
      compositionRules: [
        {
          name: "parallel_execution",
          condition: "no_dependencies",
          action: "compose_in_parallel",
          priority: 1
        }
      ],
      optimizationLevel: "advanced"
    });
  }

  /**
   * Gets proof chain by ID
   */
  getProofChain(id: string): ProofChain | undefined {
    return this.proofChains.get(id);
  }

  /**
   * Lists all proof chains
   */
  listProofChains(): ProofChain[] {
    return Array.from(this.proofChains.values());
  }

  /**
   * Validates all proof chains
   */
  async validateAllChains(): Promise<{ valid: number; invalid: number; total: number }> {
    let valid = 0;
    let invalid = 0;
    
    for (const chain of this.proofChains.values()) {
      if (chain.verificationResult) {
        valid++;
      } else {
        invalid++;
      }
    }
    
    return { valid, invalid, total: valid + invalid };
  }
}

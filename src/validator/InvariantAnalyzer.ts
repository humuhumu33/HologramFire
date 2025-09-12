import { Invariant } from "./InvariantChecker";
import { VerificationContext } from "./InvariantVerifier";
import { InvariantAnalysis, InvariantCategory, ProofStrategy } from "./AutomatedProofGenerator";
import { ccmHash } from "../crypto/ccm/CCMHash";
import { Metrics } from "../monitoring/metrics/Metrics";

/**
 * Invariant Analysis System
 * 
 * Analyzes invariants to determine optimal proof strategies,
 * dependencies, and complexity assessment.
 */

export interface InvariantPattern {
  pattern: RegExp;
  category: InvariantCategory;
  complexity: "low" | "medium" | "high";
  proofStrategy: ProofStrategy;
  dependencies: string[];
  estimatedSteps: number;
}

export interface InvariantSemantics {
  invariant: string;
  meaning: string;
  mathematicalProperties: string[];
  computationalRequirements: string[];
  securityImplications: string[];
  performanceConstraints: string[];
}

export interface InvariantDependencyGraph {
  invariant: string;
  directDependencies: string[];
  transitiveDependencies: string[];
  dependents: string[];
  dependencyLevel: number;
}

export interface InvariantComplexityAnalysis {
  invariant: string;
  syntacticComplexity: number;
  semanticComplexity: number;
  proofComplexity: number;
  verificationComplexity: number;
  overallComplexity: "low" | "medium" | "high";
  factors: string[];
}

export class InvariantAnalyzer {
  private patterns: Map<string, InvariantPattern> = new Map();
  private semantics: Map<string, InvariantSemantics> = new Map();
  private dependencyGraph: Map<string, InvariantDependencyGraph> = new Map();
  private complexityCache: Map<string, InvariantComplexityAnalysis> = new Map();
  private metrics: Metrics;

  constructor(metrics: Metrics) {
    this.metrics = metrics;
    this.initializePatterns();
    this.initializeSemantics();
    this.buildDependencyGraph();
  }

  /**
   * Analyzes an invariant comprehensively
   */
  async analyzeInvariant(
    invariant: string,
    context: VerificationContext
  ): Promise<InvariantAnalysis> {
    const startTime = Date.now();
    
    try {
      // Step 1: Pattern matching
      const pattern = this.matchPattern(invariant);
      
      // Step 2: Semantic analysis
      const semantics = this.analyzeSemantics(invariant);
      
      // Step 3: Dependency analysis
      const dependencies = this.analyzeDependencies(invariant);
      
      // Step 4: Complexity analysis
      const complexity = await this.analyzeComplexity(invariant, context);
      
      // Step 5: Proof strategy selection
      const proofStrategy = this.selectProofStrategy(invariant, pattern, semantics, complexity);
      
      // Step 6: Step estimation
      const estimatedSteps = this.estimateProofSteps(invariant, complexity, dependencies);
      
      const executionTime = Date.now() - startTime;
      this.metrics.observe("invariant_analysis_time_ms", executionTime);
      
      return {
        invariant,
        category: pattern.category,
        complexity: complexity.overallComplexity,
        proofStrategy,
        dependencies,
        estimatedSteps
      };
      
    } catch (error) {
      this.metrics.inc("invariant_analysis_error", 1);
      throw new Error(`Invariant analysis failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Matches invariant against known patterns
   */
  private matchPattern(invariant: string): InvariantPattern {
    for (const [name, pattern] of this.patterns) {
      if (pattern.pattern.test(invariant)) {
        return pattern;
      }
    }
    
    // Default pattern for unknown invariants
    return {
      pattern: /.*/,
      category: "mathematical",
      complexity: "medium",
      proofStrategy: {
        type: "mathematical",
        approach: "general_verification",
        requiredLemmas: ["basic_axioms"],
        proofSteps: [
          {
            stepType: "theorem",
            description: "Prove general theorem",
            budget: 3,
            dependencies: [],
            verification: "general_verification"
          }
        ]
      },
      dependencies: [],
      estimatedSteps: 3
    };
  }

  /**
   * Analyzes semantic meaning of invariant
   */
  private analyzeSemantics(invariant: string): InvariantSemantics {
    const cached = this.semantics.get(invariant);
    if (cached) {
      return cached;
    }
    
    // Analyze based on invariant name and context
    const meaning = this.extractMeaning(invariant);
    const mathematicalProperties = this.extractMathematicalProperties(invariant);
    const computationalRequirements = this.extractComputationalRequirements(invariant);
    const securityImplications = this.extractSecurityImplications(invariant);
    const performanceConstraints = this.extractPerformanceConstraints(invariant);
    
    const semantics: InvariantSemantics = {
      invariant,
      meaning,
      mathematicalProperties,
      computationalRequirements,
      securityImplications,
      performanceConstraints
    };
    
    this.semantics.set(invariant, semantics);
    return semantics;
  }

  /**
   * Analyzes dependencies for an invariant
   */
  private analyzeDependencies(invariant: string): string[] {
    const graph = this.dependencyGraph.get(invariant);
    if (graph) {
      return graph.transitiveDependencies;
    }
    
    // Fallback dependency analysis
    return this.extractDependenciesFromName(invariant);
  }

  /**
   * Analyzes complexity of an invariant
   */
  private async analyzeComplexity(
    invariant: string,
    context: VerificationContext
  ): Promise<InvariantComplexityAnalysis> {
    const cached = this.complexityCache.get(invariant);
    if (cached) {
      return cached;
    }
    
    const syntacticComplexity = this.analyzeSyntacticComplexity(invariant);
    const semanticComplexity = this.analyzeSemanticComplexity(invariant);
    const proofComplexity = this.analyzeProofComplexity(invariant);
    const verificationComplexity = this.analyzeVerificationComplexity(invariant, context);
    
    const overallComplexity = this.determineOverallComplexity(
      syntacticComplexity,
      semanticComplexity,
      proofComplexity,
      verificationComplexity
    );
    
    const factors = this.identifyComplexityFactors(invariant, {
      syntacticComplexity,
      semanticComplexity,
      proofComplexity,
      verificationComplexity
    });
    
    const analysis: InvariantComplexityAnalysis = {
      invariant,
      syntacticComplexity,
      semanticComplexity,
      proofComplexity,
      verificationComplexity,
      overallComplexity,
      factors
    };
    
    this.complexityCache.set(invariant, analysis);
    return analysis;
  }

  /**
   * Selects optimal proof strategy
   */
  private selectProofStrategy(
    invariant: string,
    pattern: InvariantPattern,
    semantics: InvariantSemantics,
    complexity: InvariantComplexityAnalysis
  ): ProofStrategy {
    // Use pattern-based strategy if available
    if (pattern.proofStrategy) {
      return pattern.proofStrategy;
    }
    
    // Select strategy based on complexity and semantics
    if (complexity.overallComplexity === "low") {
      return this.createLowComplexityStrategy(invariant, semantics);
    } else if (complexity.overallComplexity === "medium") {
      return this.createMediumComplexityStrategy(invariant, semantics);
    } else {
      return this.createHighComplexityStrategy(invariant, semantics);
    }
  }

  /**
   * Estimates number of proof steps
   */
  private estimateProofSteps(
    invariant: string,
    complexity: InvariantComplexityAnalysis,
    dependencies: string[]
  ): number {
    let steps = 1; // Base step
    
    // Add steps based on complexity
    steps += Math.ceil(complexity.proofComplexity / 2);
    
    // Add steps based on dependencies
    steps += dependencies.length;
    
    // Add steps based on semantic complexity
    steps += Math.ceil(complexity.semanticComplexity / 3);
    
    return Math.max(1, steps);
  }

  /**
   * Initializes invariant patterns
   */
  private initializePatterns(): void {
    // Holographic patterns
    this.patterns.set("holographic_correspondence", {
      pattern: /holographic_correspondence/,
      category: "holographic",
      complexity: "high",
      proofStrategy: {
        type: "mathematical",
        approach: "holographic_verification",
        requiredLemmas: ["holographic_axioms", "correspondence_properties"],
        proofSteps: [
          {
            stepType: "axiom",
            description: "Apply holographic correspondence axiom",
            budget: 6,
            dependencies: [],
            verification: "holographic_verification"
          },
          {
            stepType: "theorem",
            description: "Prove correspondence theorem",
            budget: 10,
            dependencies: ["holographic_axioms"],
            verification: "correspondence_verification"
          }
        ]
      },
      dependencies: ["resonance_classification", "cycle_conservation"],
      estimatedSteps: 4
    });

    // Cryptographic patterns
    this.patterns.set("signature_binding", {
      pattern: /signature_binding/,
      category: "cryptographic",
      complexity: "medium",
      proofStrategy: {
        type: "cryptographic",
        approach: "signature_verification",
        requiredLemmas: ["crypto_axioms", "signature_properties"],
        proofSteps: [
          {
            stepType: "computation",
            description: "Verify signature computation",
            budget: 7,
            dependencies: [],
            verification: "signature_computation"
          },
          {
            stepType: "verification",
            description: "Verify signature binding",
            budget: 11,
            dependencies: ["crypto_axioms"],
            verification: "binding_verification"
          }
        ]
      },
      dependencies: ["attestation_integrity"],
      estimatedSteps: 3
    });

    // Performance patterns
    this.patterns.set("throughput_bound", {
      pattern: /throughput_bound/,
      category: "performance",
      complexity: "medium",
      proofStrategy: {
        type: "computational",
        approach: "performance_measurement",
        requiredLemmas: ["performance_axioms", "bound_properties"],
        proofSteps: [
          {
            stepType: "computation",
            description: "Measure throughput",
            budget: 6,
            dependencies: [],
            verification: "throughput_measurement"
          },
          {
            stepType: "verification",
            description: "Verify throughput bound",
            budget: 9,
            dependencies: ["performance_axioms"],
            verification: "bound_verification"
          }
        ]
      },
      dependencies: ["resource_budget", "compute_bound"],
      estimatedSteps: 3
    });

    // Security patterns
    this.patterns.set("mitm_resistance", {
      pattern: /mitm_resistance/,
      category: "security",
      complexity: "high",
      proofStrategy: {
        type: "compositional",
        approach: "security_analysis",
        requiredLemmas: ["security_axioms", "resistance_properties"],
        proofSteps: [
          {
            stepType: "lemma",
            description: "Prove MITM resistance lemma",
            budget: 10,
            dependencies: [],
            verification: "resistance_lemma"
          },
          {
            stepType: "computation",
            description: "Verify resistance computation",
            budget: 14,
            dependencies: ["security_axioms"],
            verification: "resistance_computation"
          },
          {
            stepType: "verification",
            description: "Final resistance verification",
            budget: 18,
            dependencies: ["resistance_properties"],
            verification: "final_resistance"
          }
        ]
      },
      dependencies: ["forgery_resistance", "dos_resistance"],
      estimatedSteps: 5
    });
  }

  /**
   * Initializes invariant semantics
   */
  private initializeSemantics(): void {
    // Add semantic definitions for known invariants
    this.semantics.set("holographic_correspondence", {
      invariant: "holographic_correspondence",
      meaning: "Ensures mathematical correspondence between holographic representations",
      mathematicalProperties: ["bijection", "preservation", "isomorphism"],
      computationalRequirements: ["matrix_operations", "eigenvalue_computation"],
      securityImplications: ["integrity", "authenticity"],
      performanceConstraints: ["polynomial_time", "memory_bounded"]
    });

    this.semantics.set("signature_binding", {
      invariant: "signature_binding",
      meaning: "Ensures cryptographic signatures are properly bound to data",
      mathematicalProperties: ["cryptographic_hash", "digital_signature"],
      computationalRequirements: ["hash_computation", "signature_verification"],
      securityImplications: ["non_repudiation", "integrity"],
      performanceConstraints: ["constant_time", "bounded_computation"]
    });
  }

  /**
   * Builds dependency graph
   */
  private buildDependencyGraph(): void {
    // Build dependency graph based on known relationships
    const dependencies: Record<string, string[]> = {
      "holographic_correspondence": ["resonance_classification", "cycle_conservation"],
      "resonance_classification": ["cycle_conservation"],
      "signature_binding": ["attestation_integrity"],
      "attestation_integrity": ["witness_required"],
      "throughput_bound": ["resource_budget", "compute_bound"],
      "latency_bound": ["resource_budget", "compute_bound"],
      "mitm_resistance": ["forgery_resistance", "dos_resistance"],
      "forgery_resistance": ["signature_binding"],
      "dos_resistance": ["resource_budget"]
    };

    for (const [invariant, deps] of Object.entries(dependencies)) {
      const transitiveDeps = this.calculateTransitiveDependencies(deps, dependencies);
      const dependents = this.findDependents(invariant, dependencies);
      const dependencyLevel = this.calculateDependencyLevel(invariant, dependencies);

      this.dependencyGraph.set(invariant, {
        invariant,
        directDependencies: deps,
        transitiveDependencies: transitiveDeps,
        dependents,
        dependencyLevel
      });
    }
  }

  /**
   * Calculates transitive dependencies
   */
  private calculateTransitiveDependencies(
    directDeps: string[],
    allDependencies: Record<string, string[]>
  ): string[] {
    const transitive = new Set<string>();
    const visited = new Set<string>();

    const dfs = (dep: string) => {
      if (visited.has(dep)) return;
      visited.add(dep);
      
      if (allDependencies[dep]) {
        for (const subDep of allDependencies[dep]) {
          transitive.add(subDep);
          dfs(subDep);
        }
      }
    };

    for (const dep of directDeps) {
      dfs(dep);
    }

    return Array.from(transitive);
  }

  /**
   * Finds dependents of an invariant
   */
  private findDependents(
    invariant: string,
    allDependencies: Record<string, string[]>
  ): string[] {
    const dependents: string[] = [];
    
    for (const [dep, deps] of Object.entries(allDependencies)) {
      if (deps.includes(invariant)) {
        dependents.push(dep);
      }
    }
    
    return dependents;
  }

  /**
   * Calculates dependency level
   */
  private calculateDependencyLevel(
    invariant: string,
    allDependencies: Record<string, string[]>
  ): number {
    const visited = new Set<string>();
    
    const dfs = (dep: string, level: number): number => {
      if (visited.has(dep)) return level;
      visited.add(dep);
      
      let maxLevel = level;
      if (allDependencies[dep]) {
        for (const subDep of allDependencies[dep]) {
          maxLevel = Math.max(maxLevel, dfs(subDep, level + 1));
        }
      }
      
      return maxLevel;
    };
    
    return dfs(invariant, 0);
  }

  /**
   * Analyzes syntactic complexity
   */
  private analyzeSyntacticComplexity(invariant: string): number {
    let complexity = 0;
    
    // Count underscores (indicates compound concepts)
    complexity += (invariant.match(/_/g) || []).length;
    
    // Count length (longer names often indicate more complex concepts)
    complexity += Math.floor(invariant.length / 10);
    
    // Check for complex keywords
    const complexKeywords = ["composition", "transformation", "verification", "resistance"];
    for (const keyword of complexKeywords) {
      if (invariant.includes(keyword)) {
        complexity += 2;
      }
    }
    
    return complexity;
  }

  /**
   * Analyzes semantic complexity
   */
  private analyzeSemanticComplexity(invariant: string): number {
    let complexity = 0;
    
    // Check for mathematical concepts
    const mathConcepts = ["algebra", "theorem", "proof", "correspondence"];
    for (const concept of mathConcepts) {
      if (invariant.includes(concept)) {
        complexity += 2;
      }
    }
    
    // Check for cryptographic concepts
    const cryptoConcepts = ["signature", "attestation", "binding", "resistance"];
    for (const concept of cryptoConcepts) {
      if (invariant.includes(concept)) {
        complexity += 1.5;
      }
    }
    
    // Check for performance concepts
    const perfConcepts = ["bound", "limit", "threshold", "measure"];
    for (const concept of perfConcepts) {
      if (invariant.includes(concept)) {
        complexity += 1;
      }
    }
    
    return complexity;
  }

  /**
   * Analyzes proof complexity
   */
  private analyzeProofComplexity(invariant: string): number {
    let complexity = 0;
    
    // Check for proof-related concepts
    const proofConcepts = ["proof", "verification", "witness", "attestation"];
    for (const concept of proofConcepts) {
      if (invariant.includes(concept)) {
        complexity += 2;
      }
    }
    
    // Check for composition concepts
    if (invariant.includes("composition")) {
      complexity += 3;
    }
    
    // Check for resistance concepts
    if (invariant.includes("resistance")) {
      complexity += 2.5;
    }
    
    return complexity;
  }

  /**
   * Analyzes verification complexity
   */
  private analyzeVerificationComplexity(invariant: string, context: VerificationContext): number {
    let complexity = 0;
    
    // Check for computational requirements
    const computeConcepts = ["compute", "measure", "bound", "limit"];
    for (const concept of computeConcepts) {
      if (invariant.includes(concept)) {
        complexity += 1.5;
      }
    }
    
    // Check for cryptographic requirements
    const cryptoConcepts = ["crypto", "signature", "hash", "key"];
    for (const concept of cryptoConcepts) {
      if (invariant.includes(concept)) {
        complexity += 2;
      }
    }
    
    return complexity;
  }

  /**
   * Determines overall complexity
   */
  private determineOverallComplexity(
    syntactic: number,
    semantic: number,
    proof: number,
    verification: number
  ): "low" | "medium" | "high" {
    const total = syntactic + semantic + proof + verification;
    
    if (total < 5) return "low";
    if (total < 10) return "medium";
    return "high";
  }

  /**
   * Identifies complexity factors
   */
  private identifyComplexityFactors(
    invariant: string,
    complexities: {
      syntacticComplexity: number;
      semanticComplexity: number;
      proofComplexity: number;
      verificationComplexity: number;
    }
  ): string[] {
    const factors: string[] = [];
    
    if (complexities.syntacticComplexity > 2) {
      factors.push("complex_syntax");
    }
    
    if (complexities.semanticComplexity > 3) {
      factors.push("complex_semantics");
    }
    
    if (complexities.proofComplexity > 3) {
      factors.push("complex_proof");
    }
    
    if (complexities.verificationComplexity > 3) {
      factors.push("complex_verification");
    }
    
    if (invariant.includes("composition")) {
      factors.push("compositional");
    }
    
    if (invariant.includes("resistance")) {
      factors.push("security_critical");
    }
    
    return factors;
  }

  /**
   * Creates low complexity proof strategy
   */
  private createLowComplexityStrategy(
    invariant: string,
    semantics: InvariantSemantics
  ): ProofStrategy {
    return {
      type: "mathematical",
      approach: "direct_verification",
      requiredLemmas: ["basic_axioms"],
      proofSteps: [
        {
          stepType: "theorem",
          description: `Prove ${invariant}`,
          budget: 3,
          dependencies: [],
          verification: "direct_verification"
        }
      ]
    };
  }

  /**
   * Creates medium complexity proof strategy
   */
  private createMediumComplexityStrategy(
    invariant: string,
    semantics: InvariantSemantics
  ): ProofStrategy {
    return {
      type: "computational",
      approach: "step_by_step_verification",
      requiredLemmas: ["intermediate_lemmas"],
      proofSteps: [
        {
          stepType: "lemma",
          description: `Prove intermediate lemma for ${invariant}`,
          budget: 6,
          dependencies: [],
          verification: "lemma_verification"
        },
        {
          stepType: "theorem",
          description: `Apply main theorem for ${invariant}`,
          budget: 9,
          dependencies: ["intermediate_lemmas"],
          verification: "theorem_verification"
        }
      ]
    };
  }

  /**
   * Creates high complexity proof strategy
   */
  private createHighComplexityStrategy(
    invariant: string,
    semantics: InvariantSemantics
  ): ProofStrategy {
    return {
      type: "compositional",
      approach: "compositional_verification",
      requiredLemmas: ["complex_lemmas", "composition_rules"],
      proofSteps: [
        {
          stepType: "lemma",
          description: `Prove complex lemma for ${invariant}`,
          budget: 10,
          dependencies: [],
          verification: "complex_lemma_verification"
        },
        {
          stepType: "computation",
          description: `Perform computational verification for ${invariant}`,
          budget: 14,
          dependencies: ["complex_lemmas"],
          verification: "computational_verification"
        },
        {
          stepType: "verification",
          description: `Final verification for ${invariant}`,
          budget: 18,
          dependencies: ["composition_rules"],
          verification: "final_verification"
        }
      ]
    };
  }

  /**
   * Extracts meaning from invariant name
   */
  private extractMeaning(invariant: string): string {
    // Simple heuristic-based meaning extraction
    if (invariant.includes("correspondence")) {
      return "Ensures correspondence between mathematical structures";
    }
    if (invariant.includes("binding")) {
      return "Ensures proper binding of cryptographic elements";
    }
    if (invariant.includes("resistance")) {
      return "Ensures resistance against specific attacks";
    }
    if (invariant.includes("bound")) {
      return "Ensures performance bounds are maintained";
    }
    
    return `Ensures ${invariant.replace(/_/g, " ")}`;
  }

  /**
   * Extracts mathematical properties
   */
  private extractMathematicalProperties(invariant: string): string[] {
    const properties: string[] = [];
    
    if (invariant.includes("correspondence")) {
      properties.push("bijection", "preservation");
    }
    if (invariant.includes("algebra")) {
      properties.push("algebraic_structure", "closure");
    }
    if (invariant.includes("proof")) {
      properties.push("logical_consistency", "soundness");
    }
    
    return properties;
  }

  /**
   * Extracts computational requirements
   */
  private extractComputationalRequirements(invariant: string): string[] {
    const requirements: string[] = [];
    
    if (invariant.includes("compute") || invariant.includes("bound")) {
      requirements.push("performance_measurement", "resource_tracking");
    }
    if (invariant.includes("crypto") || invariant.includes("signature")) {
      requirements.push("cryptographic_computation", "hash_verification");
    }
    if (invariant.includes("measure")) {
      requirements.push("metric_collection", "statistical_analysis");
    }
    
    return requirements;
  }

  /**
   * Extracts security implications
   */
  private extractSecurityImplications(invariant: string): string[] {
    const implications: string[] = [];
    
    if (invariant.includes("resistance")) {
      implications.push("attack_resistance", "security_guarantee");
    }
    if (invariant.includes("integrity")) {
      implications.push("data_integrity", "tamper_resistance");
    }
    if (invariant.includes("signature")) {
      implications.push("authenticity", "non_repudiation");
    }
    
    return implications;
  }

  /**
   * Extracts performance constraints
   */
  private extractPerformanceConstraints(invariant: string): string[] {
    const constraints: string[] = [];
    
    if (invariant.includes("bound") || invariant.includes("limit")) {
      constraints.push("performance_bound", "resource_limit");
    }
    if (invariant.includes("throughput")) {
      constraints.push("throughput_constraint", "bandwidth_limit");
    }
    if (invariant.includes("latency")) {
      constraints.push("latency_constraint", "response_time_limit");
    }
    
    return constraints;
  }

  /**
   * Extracts dependencies from invariant name
   */
  private extractDependenciesFromName(invariant: string): string[] {
    const dependencies: string[] = [];
    
    // Simple heuristic-based dependency extraction
    if (invariant.includes("holographic")) {
      dependencies.push("resonance_classification");
    }
    if (invariant.includes("crypto") || invariant.includes("signature")) {
      dependencies.push("attestation_integrity");
    }
    if (invariant.includes("performance") || invariant.includes("bound")) {
      dependencies.push("resource_budget");
    }
    
    return dependencies;
  }

  /**
   * Gets all known invariants
   */
  getAllInvariants(): string[] {
    return Array.from(this.patterns.keys());
  }

  /**
   * Gets invariant semantics
   */
  getInvariantSemantics(invariant: string): InvariantSemantics | undefined {
    return this.semantics.get(invariant);
  }

  /**
   * Gets dependency graph for an invariant
   */
  getDependencyGraph(invariant: string): InvariantDependencyGraph | undefined {
    return this.dependencyGraph.get(invariant);
  }

  /**
   * Gets complexity analysis for an invariant
   */
  getComplexityAnalysis(invariant: string): InvariantComplexityAnalysis | undefined {
    return this.complexityCache.get(invariant);
  }
}

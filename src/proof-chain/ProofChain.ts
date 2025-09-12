import { ccmHash } from "../crypto/ccm/CCMHash";
import { Metrics } from "../monitoring/metrics/Metrics";
import { sha256Hex, stableStringify } from "../prime/Stable";
import { StandardizedMetadataReport } from "./StandardizedMetadataReport";

/**
 * Core Proof Chain Infrastructure
 * 
 * Provides atomic traceability for all computing and data transformation operations
 * in the hologram system. Every operation generates a proof that can be verified
 * and traced back to its origin.
 */

export interface ProofNode {
  id: string;
  operation: string;
  inputHash: string;
  outputHash: string;
  proof: string;
  witness: string;
  timestamp: string;
  metadata: ProofMetadata;
  parentProofs: string[];
  childProofs: string[];
}

export interface ProofMetadata {
  operationType: "computation" | "transformation" | "validation" | "verification";
  complexity: number;
  executionTimeMs: number;
  resourceUsage: ResourceUsage;
  holographicCorrespondence: string;
  invariants: string[];
  dependencies: string[];
  
  // Enhanced standardized metadata
  standardizedMetadata?: StandardizedMetadataReport;
  
  // Detailed coherence scores
  coherenceScores?: {
    overall: number;
    holographicCorrespondence: number;
    mathematicalConsistency: number;
    physicalConservation: number;
    logicalCoherence: number;
    temporalConsistency: number;
  };
  
  // Enhanced compute metrics
  computeMetrics?: {
    timeComplexity: string;
    spaceComplexity: string;
    actualComplexity: number;
    theoreticalComplexity: number;
    cpuEfficiency: number;
    memoryEfficiency: number;
    energyEfficiency: number;
    overallEfficiency: number;
    flops: {
      total: number;
      additions: number;
      multiplications: number;
      divisions: number;
      other: number;
    };
  };
  
  // Oracle metrics
  oracleMetrics?: {
    validationResult: {
      isValid: boolean;
      confidence: number;
      score: number;
      violations: string[];
      warnings: string[];
    };
    performance: {
      validationTimeMs: number;
      analysisTimeMs: number;
      totalTimeMs: number;
      memoryUsageBytes: number;
    };
    insights: {
      complexity: number;
      stability: number;
      efficiency: number;
      recommendations: string[];
    };
  };
  
  // Oculus metrics
  oculusMetrics?: {
    systemMetrics: {
      latency: {
        current: number;
        average: number;
        p95: number;
        p99: number;
        trend: 'improving' | 'stable' | 'degrading';
      };
      compute: {
        cpuUtilization: number;
        memoryUtilization: number;
        operationComplexity: number;
        efficiency: number;
      };
      energy: {
        consumptionPerOp: number;
        totalConsumption: number;
        efficiency: number;
        thermalState: number;
      };
    };
    metaAwareness: {
      coherenceScore: number;
      optimizationDecisions: string[];
      adaptiveSamplingRate: number;
    };
  };
  
  // Witness signature provenance
  witnessProvenance?: {
    signature: string;
    signatureHash: string;
    verification: {
      isValid: boolean;
      confidence: number;
      verificationTime: number;
    };
    contribution: {
      type: 'input' | 'dependency' | 'precondition' | 'intermediate' | 'output';
      weight: number;
      description: string;
    };
  };
  
  // Parent proof references for chain provenance
  parentProofs?: Array<{
    proofId: string;
    witnessSignature: string;
    contribution: {
      type: 'input' | 'dependency' | 'precondition';
      weight: number;
      description: string;
    };
    validation: {
      isValid: boolean;
      confidence: number;
      timestamp: string;
    };
  }>;
}

export interface ResourceUsage {
  cpuCycles: number;
  memoryBytes: number;
  energyJoules: number;
  networkBytes: number;
}

export interface ProofChain {
  id: string;
  rootProof: string;
  leafProofs: string[];
  totalNodes: number;
  chainHash: string;
  creationTime: string;
  lastUpdateTime: string;
  verificationStatus: "unverified" | "verified" | "failed";
  integrity: ChainIntegrity;
}

export interface ChainIntegrity {
  isComplete: boolean;
  isConsistent: boolean;
  isVerifiable: boolean;
  missingNodes: string[];
  inconsistentNodes: string[];
  verificationErrors: string[];
}

export interface ProofChainResult<T> {
  result: T;
  proofNode: ProofNode;
  chainId: string;
  verificationResult: VerificationResult;
}

export interface VerificationResult {
  isValid: boolean;
  confidence: number;
  errors: string[];
  warnings: string[];
  verificationTime: number;
  verificationMethod: string;
}

export class ProofChainManager {
  private proofNodes: Map<string, ProofNode> = new Map();
  private proofChains: Map<string, ProofChain> = new Map();
  private metrics: Metrics;
  private verificationCache: Map<string, VerificationResult> = new Map();

  constructor(metrics: Metrics) {
    this.metrics = metrics;
  }

  /**
   * Creates a new proof node for an operation
   */
  createProofNode(
    operation: string,
    input: any,
    output: any,
    metadata: Partial<ProofMetadata>,
    parentProofs: string[] = []
  ): ProofNode {
    const startTime = Date.now();
    
    const inputHash = this.hashData(input);
    const outputHash = this.hashData(output);
    const proof = this.generateProof(operation, inputHash, outputHash, metadata);
    const witness = this.generateWitness(proof, metadata);
    
    const proofNode: ProofNode = {
      id: this.generateNodeId(),
      operation,
      inputHash,
      outputHash,
      proof,
      witness,
      timestamp: new Date().toISOString(),
      metadata: {
        operationType: "computation",
        complexity: 1,
        executionTimeMs: Date.now() - startTime,
        resourceUsage: { cpuCycles: 0, memoryBytes: 0, energyJoules: 0, networkBytes: 0 },
        holographicCorrespondence: "",
        invariants: [],
        dependencies: [],
        ...metadata
      },
      parentProofs,
      childProofs: []
    };

    // Update parent nodes to include this as a child
    for (const parentId of parentProofs) {
      const parent = this.proofNodes.get(parentId);
      if (parent) {
        parent.childProofs.push(proofNode.id);
      }
    }

    this.proofNodes.set(proofNode.id, proofNode);
    this.metrics.inc("proof_nodes_created");
    
    return proofNode;
  }

  /**
   * Executes an operation with proof chain tracking
   */
  async executeWithProof<T>(
    operation: string,
    input: any,
    operationFn: (input: any) => Promise<T> | T,
    metadata: Partial<ProofMetadata> = {},
    parentProofs: string[] = []
  ): Promise<ProofChainResult<T>> {
    const startTime = Date.now();
    
    try {
      // Execute the operation
      const result = await operationFn(input);
      
      // Create proof node
      const proofNode = this.createProofNode(
        operation,
        input,
        result,
        {
          ...metadata,
          executionTimeMs: Date.now() - startTime
        },
        parentProofs
      );

      // Verify the proof
      const verificationResult = await this.verifyProofNode(proofNode);

      // Update metrics
      this.metrics.observe("operation_execution_time_ms", Date.now() - startTime);
      this.metrics.inc("operations_executed", 1, { operation });

      return {
        result,
        proofNode,
        chainId: this.getOrCreateChainId(proofNode),
        verificationResult
      };

    } catch (error) {
      this.metrics.inc("operation_failures", 1, { operation });
      throw new Error(`Operation ${operation} failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Creates a new proof chain
   */
  createProofChain(name: string, rootProof: string): ProofChain {
    const chainId = this.generateChainId();
    
    const proofChain: ProofChain = {
      id: chainId,
      rootProof,
      leafProofs: [rootProof],
      totalNodes: 1,
      chainHash: this.calculateChainHash([rootProof]),
      creationTime: new Date().toISOString(),
      lastUpdateTime: new Date().toISOString(),
      verificationStatus: "unverified",
      integrity: {
        isComplete: true,
        isConsistent: true,
        isVerifiable: true,
        missingNodes: [],
        inconsistentNodes: [],
        verificationErrors: []
      }
    };

    this.proofChains.set(chainId, proofChain);
    this.metrics.inc("proof_chains_created");
    
    return proofChain;
  }

  /**
   * Adds a proof node to an existing chain
   */
  addToChain(chainId: string, proofNodeId: string): void {
    const chain = this.proofChains.get(chainId);
    const proofNode = this.proofNodes.get(proofNodeId);
    
    if (!chain || !proofNode) {
      throw new Error(`Chain ${chainId} or proof node ${proofNodeId} not found`);
    }

    // Update chain
    chain.leafProofs = chain.leafProofs.filter(id => id !== proofNodeId);
    chain.leafProofs.push(proofNodeId);
    chain.totalNodes++;
    chain.lastUpdateTime = new Date().toISOString();
    chain.chainHash = this.calculateChainHash(this.getAllChainNodes(chainId));

    // Verify chain integrity
    this.verifyChainIntegrity(chainId);
  }

  /**
   * Verifies a proof node
   */
  async verifyProofNode(proofNode: ProofNode): Promise<VerificationResult> {
    const cacheKey = this.generateVerificationCacheKey(proofNode);
    
    if (this.verificationCache.has(cacheKey)) {
      return this.verificationCache.get(cacheKey)!;
    }

    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];

    try {
      // Verify proof structure
      if (!this.verifyProofStructure(proofNode)) {
        errors.push("Invalid proof structure");
      }

      // Verify witness
      if (!this.verifyWitness(proofNode)) {
        errors.push("Invalid witness");
      }

      // Verify parent-child relationships
      if (!this.verifyParentChildRelationships(proofNode)) {
        errors.push("Invalid parent-child relationships");
      }

      // Verify holographic correspondence
      if (!this.verifyHolographicCorrespondence(proofNode)) {
        warnings.push("Holographic correspondence verification failed");
      }

      // Verify invariants
      const invariantErrors = await this.verifyInvariants(proofNode);
      errors.push(...invariantErrors);

      const isValid = errors.length === 0;
      const confidence = this.calculateVerificationConfidence(proofNode, errors, warnings);

      const result: VerificationResult = {
        isValid,
        confidence,
        errors,
        warnings,
        verificationTime: Date.now() - startTime,
        verificationMethod: "comprehensive"
      };

      this.verificationCache.set(cacheKey, result);
      this.metrics.observe("proof_verification_time_ms", result.verificationTime);
      this.metrics.inc("proof_verifications", 1, { valid: isValid.toString() });

      return result;

    } catch (error) {
      const result: VerificationResult = {
        isValid: false,
        confidence: 0,
        errors: [`Verification failed: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        verificationTime: Date.now() - startTime,
        verificationMethod: "error"
      };

      this.verificationCache.set(cacheKey, result);
      return result;
    }
  }

  /**
   * Verifies an entire proof chain
   */
  async verifyProofChain(chainId: string): Promise<VerificationResult> {
    const chain = this.proofChains.get(chainId);
    if (!chain) {
      throw new Error(`Proof chain ${chainId} not found`);
    }

    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];

    try {
      // Get all nodes in the chain
      const allNodes = this.getAllChainNodes(chainId);
      
      // Verify each node
      for (const nodeId of allNodes) {
        const node = this.proofNodes.get(nodeId);
        if (!node) {
          errors.push(`Missing proof node: ${nodeId}`);
          continue;
        }

        const nodeVerification = await this.verifyProofNode(node);
        if (!nodeVerification.isValid) {
          errors.push(`Node ${nodeId} verification failed: ${nodeVerification.errors.join(", ")}`);
        }
        warnings.push(...nodeVerification.warnings);
      }

      // Verify chain integrity
      const integrity = this.verifyChainIntegrity(chainId);
      if (!integrity.isComplete) {
        errors.push(`Chain incomplete: missing nodes ${integrity.missingNodes.join(", ")}`);
      }
      if (!integrity.isConsistent) {
        errors.push(`Chain inconsistent: inconsistent nodes ${integrity.inconsistentNodes.join(", ")}`);
      }

      const isValid = errors.length === 0;
      const confidence = this.calculateChainVerificationConfidence(chain, errors, warnings);

      const result: VerificationResult = {
        isValid,
        confidence,
        errors,
        warnings,
        verificationTime: Date.now() - startTime,
        verificationMethod: "chain_verification"
      };

      // Update chain verification status
      chain.verificationStatus = isValid ? "verified" : "failed";
      chain.integrity.verificationErrors = errors;

      this.metrics.observe("chain_verification_time_ms", result.verificationTime);
      this.metrics.inc("chain_verifications", 1, { valid: isValid.toString() });

      return result;

    } catch (error) {
      return {
        isValid: false,
        confidence: 0,
        errors: [`Chain verification failed: ${error instanceof Error ? error.message : String(error)}`],
        warnings: [],
        verificationTime: Date.now() - startTime,
        verificationMethod: "error"
      };
    }
  }

  /**
   * Traces the provenance of a result back to its origin
   */
  traceProvenance(proofNodeId: string): ProofNode[] {
    const provenance: ProofNode[] = [];
    const visited = new Set<string>();
    
    const traceRecursive = (nodeId: string) => {
      if (visited.has(nodeId)) return;
      visited.add(nodeId);
      
      const node = this.proofNodes.get(nodeId);
      if (!node) return;
      
      provenance.push(node);
      
      // Trace to parents
      for (const parentId of node.parentProofs) {
        traceRecursive(parentId);
      }
    };

    traceRecursive(proofNodeId);
    
    // Sort by timestamp to get chronological order
    return provenance.sort((a, b) => new Date(a.timestamp).getTime() - new Date(b.timestamp).getTime());
  }

  /**
   * Gets all proof nodes in a chain
   */
  getAllChainNodes(chainId: string): string[] {
    const chain = this.proofChains.get(chainId);
    if (!chain) return [];

    const allNodes = new Set<string>();
    
    const collectNodes = (nodeId: string) => {
      if (allNodes.has(nodeId)) return;
      allNodes.add(nodeId);
      
      const node = this.proofNodes.get(nodeId);
      if (node) {
        for (const childId of node.childProofs) {
          collectNodes(childId);
        }
      }
    };

    collectNodes(chain.rootProof);
    return Array.from(allNodes);
  }

  // Private helper methods

  private hashData(data: any): string {
    return ccmHash(data, "proof_input");
  }

  private generateProof(operation: string, inputHash: string, outputHash: string, metadata: any): string {
    const proofData = {
      operation,
      inputHash,
      outputHash,
      metadata: ccmHash(metadata, "proof_metadata"),
      timestamp: new Date().toISOString()
    };
    return ccmHash(proofData, "proof_generation");
  }

  private generateWitness(proof: string, metadata: any): string {
    const witnessData = {
      proof,
      metadata: ccmHash(metadata, "witness_metadata"),
      timestamp: new Date().toISOString()
    };
    return ccmHash(witnessData, "witness_generation");
  }

  private generateNodeId(): string {
    return ccmHash({ timestamp: Date.now(), random: Math.random() }, "node_id");
  }

  private generateChainId(): string {
    return ccmHash({ timestamp: Date.now(), random: Math.random() }, "chain_id");
  }


  private calculateChainHash(nodeIds: string[]): string {
    return ccmHash({ nodes: nodeIds.sort() }, "chain_hash");
  }

  private verifyProofStructure(proofNode: ProofNode): boolean {
    return !!(
      proofNode.id &&
      proofNode.operation &&
      proofNode.inputHash &&
      proofNode.outputHash &&
      proofNode.proof &&
      proofNode.witness &&
      proofNode.timestamp
    );
  }

  private verifyWitness(proofNode: ProofNode): boolean {
    const expectedWitness = this.generateWitness(proofNode.proof, proofNode.metadata);
    return proofNode.witness === expectedWitness;
  }

  private verifyParentChildRelationships(proofNode: ProofNode): boolean {
    // Verify that all parent nodes exist and reference this node as a child
    for (const parentId of proofNode.parentProofs) {
      const parent = this.proofNodes.get(parentId);
      if (!parent || !parent.childProofs.includes(proofNode.id)) {
        return false;
      }
    }
    return true;
  }

  private verifyHolographicCorrespondence(proofNode: ProofNode): boolean {
    // Verify holographic correspondence using existing hologram oracle
    try {
      const correspondence = ccmHash(proofNode.metadata, "holographic_correspondence");
      return proofNode.metadata.holographicCorrespondence === correspondence;
    } catch {
      return false;
    }
  }

  private async verifyInvariants(proofNode: ProofNode): Promise<string[]> {
    const errors: string[] = [];
    
    // Verify each invariant
    for (const invariant of proofNode.metadata.invariants) {
      try {
        // This would integrate with the existing invariant verification system
        // For now, we'll do a basic check
        if (!invariant || typeof invariant !== 'string') {
          errors.push(`Invalid invariant: ${invariant}`);
        }
      } catch (error) {
        errors.push(`Invariant verification failed for ${invariant}: ${error instanceof Error ? error.message : String(error)}`);
      }
    }
    
    return errors;
  }

  private calculateVerificationConfidence(proofNode: ProofNode, errors: string[], warnings: string[]): number {
    let confidence = 1.0;
    
    // Reduce confidence for errors
    confidence -= errors.length * 0.2;
    
    // Reduce confidence for warnings
    confidence -= warnings.length * 0.05;
    
    // Factor in metadata quality
    if (proofNode.metadata.invariants.length === 0) {
      confidence -= 0.1;
    }
    
    return Math.max(0, Math.min(1, confidence));
  }

  private calculateChainVerificationConfidence(chain: ProofChain, errors: string[], warnings: string[]): number {
    let confidence = 1.0;
    
    // Reduce confidence for errors
    confidence -= errors.length * 0.15;
    
    // Reduce confidence for warnings
    confidence -= warnings.length * 0.03;
    
    // Factor in chain completeness
    if (!chain.integrity.isComplete) {
      confidence -= 0.2;
    }
    
    if (!chain.integrity.isConsistent) {
      confidence -= 0.3;
    }
    
    return Math.max(0, Math.min(1, confidence));
  }

  private verifyChainIntegrity(chainId: string): ChainIntegrity {
    const chain = this.proofChains.get(chainId);
    if (!chain) {
      return {
        isComplete: false,
        isConsistent: false,
        isVerifiable: false,
        missingNodes: [],
        inconsistentNodes: [],
        verificationErrors: ["Chain not found"]
      };
    }

    const allNodes = this.getAllChainNodes(chainId);
    const missingNodes: string[] = [];
    const inconsistentNodes: string[] = [];
    const verificationErrors: string[] = [];

    // Check for missing nodes
    for (const nodeId of allNodes) {
      if (!this.proofNodes.has(nodeId)) {
        missingNodes.push(nodeId);
      }
    }

    // Check for inconsistent nodes
    for (const nodeId of allNodes) {
      const node = this.proofNodes.get(nodeId);
      if (node) {
        // Check parent-child consistency
        for (const parentId of node.parentProofs) {
          const parent = this.proofNodes.get(parentId);
          if (!parent || !parent.childProofs.includes(nodeId)) {
            inconsistentNodes.push(nodeId);
            break;
          }
        }
      }
    }

    const isComplete = missingNodes.length === 0;
    const isConsistent = inconsistentNodes.length === 0;
    const isVerifiable = isComplete && isConsistent;

    const integrity: ChainIntegrity = {
      isComplete,
      isConsistent,
      isVerifiable,
      missingNodes,
      inconsistentNodes,
      verificationErrors
    };

    chain.integrity = integrity;
    return integrity;
  }

  private generateVerificationCacheKey(proofNode: ProofNode): string {
    return ccmHash({ id: proofNode.id, proof: proofNode.proof }, "verification_cache");
  }

  // Public accessor methods for oracle coherence
  public getProofNode(nodeId: string): ProofNode | undefined {
    return this.proofNodes.get(nodeId);
  }

  public getProofChain(chainId: string): ProofChain | undefined {
    return this.proofChains.get(chainId);
  }

  public getAllProofNodes(): Map<string, ProofNode> {
    return this.proofNodes;
  }

  public getAllProofChains(): Map<string, ProofChain> {
    return this.proofChains;
  }

  public getOrCreateChainId(proofNode: ProofNode): string {
    // Find existing chain or create new one
    for (const [chainId, chain] of this.proofChains.entries()) {
      if (chain.leafProofs.includes(proofNode.id)) {
        return chainId;
      }
    }
    
    // Create new chain
    const chainId = ccmHash(proofNode, "new_chain");
    const newChain: ProofChain = {
      id: chainId,
      rootProof: proofNode.id,
      leafProofs: [proofNode.id],
      totalNodes: 1,
      chainHash: proofNode.proof,
      creationTime: proofNode.timestamp,
      lastUpdateTime: proofNode.timestamp,
      verificationStatus: "unverified",
      integrity: {
        isComplete: true,
        isConsistent: true,
        isVerifiable: true,
        missingNodes: [],
        inconsistentNodes: [],
        verificationErrors: []
      }
    };
    
    this.proofChains.set(chainId, newChain);
    return chainId;
  }
}

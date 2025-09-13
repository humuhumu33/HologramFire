/**
 * Witness Signature Provenance Tracking System
 * 
 * Provides comprehensive provenance tracking for proof chains with witness signature
 * verification, ensuring full traceability of proof dependencies and their contributions
 * to computational results.
 */

import { ccmHash } from "../crypto/ccm/CCMHash";
import { Metrics } from "../monitoring/metrics/Metrics";
import { holoSign, HoloSig } from "../crypto/signature/HoloSig";
import { alphaAttest, AlphaAttestation } from "../crypto/attestation/Alpha";

/**
 * Witness signature for proof provenance
 */
export interface WitnessSignature {
  // Signature data
  signature: string;
  signatureHash: string;
  
  // Signature metadata
  metadata: {
    algorithm: string;
    keyId: string;
    timestamp: string;
    domain: string;
    version: string;
  };
  
  // Signature verification
  verification: {
    isValid: boolean;
    confidence: number;
    verificationTime: number;
    verificationMethod: string;
  };
  
  // Holographic correspondence
  holographicCorrespondence: string;
}

/**
 * Provenance entry for a proof in the chain
 */
export interface ProvenanceEntry {
  // Proof identification
  proofId: string;
  proofHash: string;
  
  // Witness signature
  witnessSignature: WitnessSignature;
  
  // Contribution to the computation
  contribution: {
    type: 'input' | 'dependency' | 'precondition' | 'intermediate' | 'output';
    weight: number;
    description: string;
    dataHash: string;
    transformationHash?: string;
  };
  
  // Validation status
  validation: {
    isValid: boolean;
    confidence: number;
    timestamp: string;
    validator: string;
  };
  
  // Chain position
  position: {
    depth: number;
    index: number;
    parentIndices: number[];
    childIndices: number[];
  };
  
  // Metadata
  metadata: {
    creationTime: string;
    lastUpdateTime: string;
    operationType: string;
    complexity: number;
  };
}

/**
 * Complete provenance chain
 */
export interface ProvenanceChain {
  // Chain identification
  chainId: string;
  rootProofId: string;
  leafProofIds: string[];
  
  // Chain structure
  entries: ProvenanceEntry[];
  totalEntries: number;
  maxDepth: number;
  
  // Chain integrity
  integrity: {
    isComplete: boolean;
    isConsistent: boolean;
    isVerifiable: boolean;
    missingEntries: string[];
    inconsistentEntries: string[];
    verificationErrors: string[];
  };
  
  // Chain metadata
  metadata: {
    creationTime: string;
    lastUpdateTime: string;
    totalOperations: number;
    totalComplexity: number;
    averageConfidence: number;
  };
  
  // Holographic correspondence
  holographicCorrespondence: string;
}

/**
 * Witness signature provenance tracker
 */
export class WitnessSignatureProvenanceTracker {
  private metrics: Metrics;
  private provenanceChains: Map<string, ProvenanceChain> = new Map();
  private witnessSignatures: Map<string, WitnessSignature> = new Map();
  
  constructor(metrics: Metrics) {
    this.metrics = metrics;
  }
  
  /**
   * Create a new provenance chain
   */
  createProvenanceChain(chainId: string, rootProofId: string): ProvenanceChain {
    const chain: ProvenanceChain = {
      chainId,
      rootProofId,
      leafProofIds: [rootProofId],
      entries: [],
      totalEntries: 0,
      maxDepth: 0,
      integrity: {
        isComplete: true,
        isConsistent: true,
        isVerifiable: true,
        missingEntries: [],
        inconsistentEntries: [],
        verificationErrors: []
      },
      metadata: {
        creationTime: new Date().toISOString(),
        lastUpdateTime: new Date().toISOString(),
        totalOperations: 0,
        totalComplexity: 0,
        averageConfidence: 0
      },
      holographicCorrespondence: ""
    };
    
    this.provenanceChains.set(chainId, chain);
    this.metrics.inc("provenance_chains_created", 1);
    
    return chain;
  }
  
  /**
   * Add a proof to the provenance chain with witness signature
   */
  async addProofToChain(
    chainId: string,
    proofId: string,
    proofData: any,
    contribution: {
      type: 'input' | 'dependency' | 'precondition' | 'intermediate' | 'output';
      weight: number;
      description: string;
      dataHash?: string;
      transformationHash?: string;
    },
    parentProofIds: string[] = []
  ): Promise<ProvenanceEntry> {
    const startTime = Date.now();
    
    try {
      const chain = this.provenanceChains.get(chainId);
      if (!chain) {
        throw new Error(`Provenance chain ${chainId} not found`);
      }
      
      // Generate witness signature
      const witnessSignature = await this.generateWitnessSignature(proofId, proofData);
      
      // Calculate position in chain
      const position = this.calculatePosition(chain, parentProofIds);
      
      // Validate the proof
      const validation = await this.validateProof(proofId, proofData, witnessSignature);
      
      // Create provenance entry
      const entry: ProvenanceEntry = {
        proofId,
        proofHash: ccmHash(proofData, "proof_hash"),
        witnessSignature,
        contribution: {
          ...contribution,
          dataHash: contribution.dataHash || ccmHash(proofData, "data_hash")
        },
        validation,
        position,
        metadata: {
          creationTime: new Date().toISOString(),
          lastUpdateTime: new Date().toISOString(),
          operationType: this.determineOperationType(proofData),
          complexity: this.calculateComplexity(proofData)
        }
      };
      
      // Add to chain
      chain.entries.push(entry);
      chain.totalEntries++;
      chain.maxDepth = Math.max(chain.maxDepth, position.depth);
      chain.metadata.lastUpdateTime = new Date().toISOString();
      chain.metadata.totalOperations++;
      chain.metadata.totalComplexity += entry.metadata.complexity;
      
      // Update leaf proofs
      this.updateLeafProofs(chain, proofId, parentProofIds);
      
      // Update chain integrity
      this.updateChainIntegrity(chain);
      
      // Update holographic correspondence
      chain.holographicCorrespondence = this.generateChainHolographicCorrespondence(chain);
      
      // Store witness signature
      this.witnessSignatures.set(proofId, witnessSignature);
      
      // Record metrics
      this.metrics.observe("provenance_entry_creation_time_ms", Date.now() - startTime);
      this.metrics.inc("provenance_entries_created", 1);
      
      return entry;
      
    } catch (error) {
      this.metrics.inc("provenance_entry_errors", 1);
      throw new Error(`Failed to add proof to provenance chain: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
  
  /**
   * Verify the integrity of a provenance chain
   */
  async verifyProvenanceChain(chainId: string): Promise<{
    isValid: boolean;
    confidence: number;
    errors: string[];
    warnings: string[];
    verificationTime: number;
  }> {
    const startTime = Date.now();
    const errors: string[] = [];
    const warnings: string[] = [];
    
    try {
      const chain = this.provenanceChains.get(chainId);
      if (!chain) {
        errors.push(`Provenance chain ${chainId} not found`);
        return {
          isValid: false,
          confidence: 0,
          errors,
          warnings,
          verificationTime: Date.now() - startTime
        };
      }
      
      // Verify each entry in the chain
      for (const entry of chain.entries) {
        const entryVerification = await this.verifyProvenanceEntry(entry);
        if (!entryVerification.isValid) {
          errors.push(`Entry ${entry.proofId}: ${entryVerification.errors.join(', ')}`);
        }
        if (entryVerification.warnings.length > 0) {
          warnings.push(`Entry ${entry.proofId}: ${entryVerification.warnings.join(', ')}`);
        }
      }
      
      // Verify chain structure
      const structureVerification = this.verifyChainStructure(chain);
      if (!structureVerification.isValid) {
        errors.push(`Chain structure: ${structureVerification.errors.join(', ')}`);
      }
      
      // Verify witness signatures
      const signatureVerification = await this.verifyWitnessSignatures(chain);
      if (!signatureVerification.isValid) {
        errors.push(`Witness signatures: ${signatureVerification.errors.join(', ')}`);
      }
      
      // Calculate overall confidence
      const confidence = this.calculateChainConfidence(chain, errors.length);
      
      const isValid = errors.length === 0;
      
      // Record metrics
      this.metrics.observe("provenance_chain_verification_time_ms", Date.now() - startTime);
      this.metrics.inc("provenance_chain_verifications", 1);
      if (isValid) {
        this.metrics.inc("provenance_chain_verifications_valid", 1);
      } else {
        this.metrics.inc("provenance_chain_verifications_invalid", 1);
      }
      
      return {
        isValid,
        confidence,
        errors,
        warnings,
        verificationTime: Date.now() - startTime
      };
      
    } catch (error) {
      this.metrics.inc("provenance_chain_verification_errors", 1);
      return {
        isValid: false,
        confidence: 0,
        errors: [`Verification failed: ${error instanceof Error ? error.message : String(error)}`],
        warnings,
        verificationTime: Date.now() - startTime
      };
    }
  }
  
  /**
   * Get provenance chain by ID
   */
  getProvenanceChain(chainId: string): ProvenanceChain | undefined {
    return this.provenanceChains.get(chainId);
  }
  
  /**
   * Get witness signature by proof ID
   */
  getWitnessSignature(proofId: string): WitnessSignature | undefined {
    return this.witnessSignatures.get(proofId);
  }
  
  /**
   * Get all provenance chains
   */
  getAllProvenanceChains(): ProvenanceChain[] {
    return Array.from(this.provenanceChains.values());
  }
  
  /**
   * Generate witness signature for a proof
   */
  private async generateWitnessSignature(proofId: string, proofData: any): Promise<WitnessSignature> {
    const startTime = Date.now();
    
    try {
      // Generate signature using holo signature
      const signature = await holoSign(proofData, proofId, "witness_secret");
      
      // Generate signature hash
      const signatureHash = ccmHash(signature, "signature_hash");
      
      // Verify the signature
      const verification = await this.verifyWitnessSignature(signature, proofData, proofId);
      
      const witnessSignature: WitnessSignature = {
        signature: signature.sig,
        signatureHash,
        metadata: {
          algorithm: "holo_signature",
          keyId: signature.module || "",
          timestamp: new Date().toISOString(),
          domain: "proof_witness",
          version: "1.0.0"
        },
        verification: {
          isValid: verification.isValid,
          confidence: verification.confidence,
          verificationTime: Date.now() - startTime,
          verificationMethod: "holo_signature"
        },
        holographicCorrespondence: ccmHash({
          signature: signature.sig,
          proofId,
          timestamp: Date.now()
        }, "witness_signature")
      };
      
      return witnessSignature;
      
    } catch (error) {
      return {
        signature: "",
        signatureHash: "",
        metadata: {
          algorithm: "holo_signature",
          keyId: "",
          timestamp: new Date().toISOString(),
          domain: "proof_witness",
          version: "1.0.0"
        },
        verification: {
          isValid: false,
          confidence: 0,
          verificationTime: Date.now() - startTime,
          verificationMethod: "holo_signature"
        },
        holographicCorrespondence: ""
      };
    }
  }
  
  /**
   * Verify a witness signature
   */
  private async verifyWitnessSignature(
    signature: HoloSig,
    proofData: any,
    proofId: string
  ): Promise<{ isValid: boolean; confidence: number }> {
    try {
      // This would normally verify the signature using the holo signature verification
      // For now, we'll do a basic validation
      const isValid = signature.sig.length > 0 && signature.module && signature.hash;
      const confidence = isValid ? 1.0 : 0.0;
      
      return { isValid: Boolean(isValid), confidence };
      
    } catch (error) {
      return { isValid: false, confidence: 0 };
    }
  }
  
  /**
   * Calculate position in the provenance chain
   */
  private calculatePosition(chain: ProvenanceChain, parentProofIds: string[]): {
    depth: number;
    index: number;
    parentIndices: number[];
    childIndices: number[];
  } {
    const index = chain.entries.length;
    const parentIndices = parentProofIds.map(parentId => 
      chain.entries.findIndex(entry => entry.proofId === parentId)
    ).filter(idx => idx !== -1);
    
    const depth = parentIndices.length > 0 
      ? Math.max(...parentIndices.map(idx => chain.entries[idx].position.depth)) + 1
      : 0;
    
    return {
      depth,
      index,
      parentIndices,
      childIndices: [] // Will be updated when children are added
    };
  }
  
  /**
   * Validate a proof
   */
  private async validateProof(
    proofId: string,
    proofData: any,
    witnessSignature: WitnessSignature
  ): Promise<{
    isValid: boolean;
    confidence: number;
    timestamp: string;
    validator: string;
  }> {
    const isValid = witnessSignature.verification.isValid && 
                   witnessSignature.signature.length > 0 &&
                   proofData !== null;
    
    const confidence = witnessSignature.verification.confidence * (isValid ? 1.0 : 0.0);
    
    return {
      isValid,
      confidence,
      timestamp: new Date().toISOString(),
      validator: "WitnessSignatureProvenanceTracker"
    };
  }
  
  /**
   * Determine operation type from proof data
   */
  private determineOperationType(proofData: any): string {
    if (typeof proofData === 'object' && proofData !== null) {
      if (proofData.operation) return proofData.operation;
      if (proofData.type) return proofData.type;
      if (proofData.algorithm) return 'computation';
      if (proofData.transformation) return 'transformation';
    }
    return 'unknown';
  }
  
  /**
   * Calculate complexity of proof data
   */
  private calculateComplexity(proofData: any): number {
    const dataString = JSON.stringify(proofData);
    return dataString.length;
  }
  
  /**
   * Update leaf proofs in the chain
   */
  private updateLeafProofs(chain: ProvenanceChain, proofId: string, parentProofIds: string[]): void {
    // Remove parent proofs from leaf proofs if they exist
    chain.leafProofIds = chain.leafProofIds.filter(id => !parentProofIds.includes(id));
    
    // Add this proof as a leaf
    chain.leafProofIds.push(proofId);
  }
  
  /**
   * Update chain integrity
   */
  private updateChainIntegrity(chain: ProvenanceChain): void {
    const missingEntries: string[] = [];
    const inconsistentEntries: string[] = [];
    const verificationErrors: string[] = [];
    
    // Check for missing entries
    for (const entry of chain.entries) {
      if (!entry.witnessSignature.signature) {
        missingEntries.push(entry.proofId);
      }
      if (!entry.validation.isValid) {
        inconsistentEntries.push(entry.proofId);
      }
      if (entry.validation.confidence < 0.5) {
        verificationErrors.push(`Low confidence for ${entry.proofId}: ${entry.validation.confidence}`);
      }
    }
    
    chain.integrity = {
      isComplete: missingEntries.length === 0,
      isConsistent: inconsistentEntries.length === 0,
      isVerifiable: verificationErrors.length === 0,
      missingEntries,
      inconsistentEntries,
      verificationErrors
    };
    
    // Update average confidence
    if (chain.entries.length > 0) {
      chain.metadata.averageConfidence = chain.entries.reduce(
        (sum, entry) => sum + entry.validation.confidence, 0
      ) / chain.entries.length;
    }
  }
  
  /**
   * Generate holographic correspondence for the chain
   */
  private generateChainHolographicCorrespondence(chain: ProvenanceChain): string {
    return ccmHash({
      chainId: chain.chainId,
      totalEntries: chain.totalEntries,
      maxDepth: chain.maxDepth,
      integrity: chain.integrity,
      metadata: chain.metadata,
      entries: chain.entries.map(entry => ({
        proofId: entry.proofId,
        witnessSignature: entry.witnessSignature.signatureHash,
        contribution: entry.contribution.type,
        validation: entry.validation.isValid
      }))
    }, "provenance_chain");
  }
  
  /**
   * Verify a provenance entry
   */
  private async verifyProvenanceEntry(entry: ProvenanceEntry): Promise<{
    isValid: boolean;
    errors: string[];
    warnings: string[];
  }> {
    const errors: string[] = [];
    const warnings: string[] = [];
    
    // Check witness signature
    if (!entry.witnessSignature.signature) {
      errors.push("Missing witness signature");
    }
    
    if (!entry.witnessSignature.verification.isValid) {
      errors.push("Invalid witness signature");
    }
    
    if (entry.witnessSignature.verification.confidence < 0.8) {
      warnings.push(`Low witness signature confidence: ${entry.witnessSignature.verification.confidence}`);
    }
    
    // Check validation
    if (!entry.validation.isValid) {
      errors.push("Proof validation failed");
    }
    
    if (entry.validation.confidence < 0.5) {
      warnings.push(`Low validation confidence: ${entry.validation.confidence}`);
    }
    
    // Check contribution
    if (entry.contribution.weight <= 0) {
      warnings.push("Zero or negative contribution weight");
    }
    
    return {
      isValid: errors.length === 0,
      errors,
      warnings
    };
  }
  
  /**
   * Verify chain structure
   */
  private verifyChainStructure(chain: ProvenanceChain): {
    isValid: boolean;
    errors: string[];
  } {
    const errors: string[] = [];
    
    // Check that all parent indices are valid
    for (const entry of chain.entries) {
      for (const parentIndex of entry.position.parentIndices) {
        if (parentIndex < 0 || parentIndex >= chain.entries.length) {
          errors.push(`Invalid parent index ${parentIndex} for entry ${entry.proofId}`);
        }
      }
    }
    
    // Check that root proof exists
    const rootEntry = chain.entries.find(entry => entry.proofId === chain.rootProofId);
    if (!rootEntry) {
      errors.push(`Root proof ${chain.rootProofId} not found in entries`);
    }
    
    // Check that leaf proofs exist
    for (const leafId of chain.leafProofIds) {
      const leafEntry = chain.entries.find(entry => entry.proofId === leafId);
      if (!leafEntry) {
        errors.push(`Leaf proof ${leafId} not found in entries`);
      }
    }
    
    return {
      isValid: errors.length === 0,
      errors
    };
  }
  
  /**
   * Verify witness signatures in the chain
   */
  private async verifyWitnessSignatures(chain: ProvenanceChain): Promise<{
    isValid: boolean;
    errors: string[];
  }> {
    const errors: string[] = [];
    
    for (const entry of chain.entries) {
      if (!entry.witnessSignature.verification.isValid) {
        errors.push(`Invalid witness signature for ${entry.proofId}`);
      }
    }
    
    return {
      isValid: errors.length === 0,
      errors
    };
  }
  
  /**
   * Calculate chain confidence
   */
  private calculateChainConfidence(chain: ProvenanceChain, errorCount: number): number {
    if (chain.entries.length === 0) return 0;
    
    const baseConfidence = chain.metadata.averageConfidence;
    const errorPenalty = errorCount / chain.entries.length;
    
    return Math.max(0, baseConfidence - errorPenalty);
  }
}

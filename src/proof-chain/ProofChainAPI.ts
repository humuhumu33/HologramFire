import { ProofChainManager } from "./ProofChain";
import { DataTransformationProofSystem, DataTransformation } from "./DataTransformationProofs";
import { ComputationProofSystem, Computation } from "./ComputationProofs";
import { ProofChainMonitor, MonitoringConfig, ComplianceReport, ProvenanceTrace } from "./ProofChainMonitor";
import { Metrics } from "../monitoring/metrics/Metrics";
import { ccmHash } from "../crypto/ccm/CCMHash";

/**
 * Easy-to-Use Proof Chain API
 * 
 * Provides a simple, intuitive interface for all proof chain operations.
 * Enables developers to easily add proof generation to their operations
 * and verify the chain of proof provenance.
 */

export interface ProofChainAPIConfig {
  enableMonitoring: boolean;
  enableCompliance: boolean;
  enableProvenance: boolean;
  monitoringConfig?: Partial<MonitoringConfig>;
  autoStartMonitoring?: boolean;
}

export interface OperationResult<T> {
  result: T;
  proofNodeId: string;
  chainId: string;
  verificationStatus: "verified" | "failed" | "pending";
  confidence: number;
  executionTimeMs: number;
}

export interface ChainVerificationResult {
  chainId: string;
  isValid: boolean;
  confidence: number;
  totalNodes: number;
  verifiedNodes: number;
  failedNodes: number;
  issues: string[];
  verificationTimeMs: number;
}

export interface ProvenanceVerificationResult {
  traceId: string;
  isValid: boolean;
  confidence: number;
  pathLength: number;
  isComplete: boolean;
  issues: string[];
  verificationTimeMs: number;
}

export class ProofChainAPI {
  private proofChainManager: ProofChainManager;
  private dataTransformationSystem: DataTransformationProofSystem;
  private computationSystem: ComputationProofSystem;
  private monitor: ProofChainMonitor;
  private metrics: Metrics;
  private config: ProofChainAPIConfig;

  constructor(config: Partial<ProofChainAPIConfig> = {}) {
    this.metrics = new Metrics();
    this.config = {
      enableMonitoring: true,
      enableCompliance: true,
      enableProvenance: true,
      autoStartMonitoring: true,
      ...config
    };

    // Initialize core systems
    this.proofChainManager = new ProofChainManager(this.metrics);
    this.dataTransformationSystem = new DataTransformationProofSystem(this.proofChainManager, this.metrics);
    this.computationSystem = new ComputationProofSystem(this.proofChainManager, this.metrics);

    // Initialize monitoring
    this.monitor = new ProofChainMonitor(
      this.proofChainManager,
      this.metrics,
      this.config.monitoringConfig
    );

    if (this.config.autoStartMonitoring) {
      this.monitor.startMonitoring();
    }
  }

  /**
   * Executes a data transformation with proof generation
   */
  async transformData<T, R>(
    operation: string,
    input: T,
    transformFn: (input: T) => Promise<R> | R,
    options: {
      transformationType?: "map" | "filter" | "reduce" | "aggregate" | "normalize" | "encode" | "decode" | "validate";
      invariants?: string[];
      parentProofs?: string[];
    } = {}
  ): Promise<OperationResult<R>> {
    const startTime = Date.now();

    try {
      const transformation: DataTransformation = {
        operation,
        input,
        output: null, // Will be set by the system
        transformationType: options.transformationType || "map",
        invariants: options.invariants || [],
        metadata: {
          inputSize: 0,
          outputSize: 0,
          dataIntegrity: false,
          schemaValidation: false,
          holographicCorrespondence: "",
          performanceMetrics: {
            executionTimeMs: 0,
            memoryUsageBytes: 0,
            cpuCycles: 0,
            energyConsumptionJoules: 0
          }
        }
      };

      const result = await this.dataTransformationSystem.transformWithProof(
        transformation,
        transformFn,
        options.parentProofs || []
      );

      return {
        result: result.result,
        proofNodeId: result.proofNode.id,
        chainId: result.chainId,
        verificationStatus: result.verificationResult.isValid ? "verified" : "failed",
        confidence: result.verificationResult.confidence,
        executionTimeMs: Date.now() - startTime
      };

    } catch (error) {
      throw new Error(`Data transformation failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Executes a computation with proof generation
   */
  async compute<T, R>(
    operation: string,
    input: T,
    computeFn: (input: T) => Promise<R> | R,
    options: {
      computationType?: "algorithm" | "calculation" | "optimization" | "simulation" | "analysis" | "prediction" | "verification";
      algorithm?: string;
      parameters?: {
        precision?: number;
        iterations?: number;
        tolerance?: number;
        maxSteps?: number;
        convergenceCriteria?: string;
        optimizationTarget?: string;
      };
      invariants?: string[];
      parentProofs?: string[];
    } = {}
  ): Promise<OperationResult<R>> {
    const startTime = Date.now();

    try {
      const computation: Computation = {
        operation,
        input,
        output: null, // Will be set by the system
        computationType: options.computationType || "calculation",
        algorithm: options.algorithm || "default",
        parameters: {
          precision: 1e-6,
          ...options.parameters
        },
        invariants: options.invariants || [],
        metadata: {
          algorithmComplexity: 1,
          computationalComplexity: "O(1)",
          accuracy: 1.0,
          convergence: true,
          stability: 1.0,
          holographicCorrespondence: "",
          performanceMetrics: {
            executionTimeMs: 0,
            memoryUsageBytes: 0,
            cpuCycles: 0,
            energyConsumptionJoules: 0,
            cacheHits: 0,
            cacheMisses: 0,
            floatingPointOperations: 0
          },
          mathematicalProperties: {
            isDeterministic: true,
            isReversible: false,
            isAssociative: false,
            isCommutative: false,
            hasFixedPoint: false
          }
        }
      };

      const result = await this.computationSystem.computeWithProof(
        computation,
        computeFn,
        options.parentProofs || []
      );

      return {
        result: result.result,
        proofNodeId: result.proofNode.id,
        chainId: result.chainId,
        verificationStatus: result.verificationResult.isValid ? "verified" : "failed",
        confidence: result.verificationResult.confidence,
        executionTimeMs: Date.now() - startTime
      };

    } catch (error) {
      throw new Error(`Computation failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Chains multiple operations together
   */
  async chainOperations<T>(
    operations: Array<{
      type: "transform" | "compute";
      operation: string;
      transformFn?: (input: any) => Promise<any> | any;
      computeFn?: (input: any) => Promise<any> | any;
      options?: any;
    }>,
    initialInput: T
  ): Promise<OperationResult<any>[]> {
    const results: OperationResult<any>[] = [];
    let currentInput = initialInput;
    let parentProofs: string[] = [];

    for (const op of operations) {
      let result: OperationResult<any>;

      if (op.type === "transform" && op.transformFn) {
        result = await this.transformData(
          op.operation,
          currentInput,
          op.transformFn,
          { ...op.options, parentProofs }
        );
      } else if (op.type === "compute" && op.computeFn) {
        result = await this.compute(
          op.operation,
          currentInput,
          op.computeFn,
          { ...op.options, parentProofs }
        );
      } else {
        throw new Error(`Invalid operation type or missing function for operation: ${op.operation}`);
      }

      results.push(result);
      currentInput = result.result;
      parentProofs = [result.proofNodeId];
    }

    return results;
  }

  /**
   * Verifies a proof chain
   */
  async verifyChain(chainId: string): Promise<ChainVerificationResult> {
    const startTime = Date.now();

    try {
      const verificationResult = await this.proofChainManager.verifyProofChain(chainId);
      const chain = this.proofChainManager.getProofChain(chainId);
      
      if (!chain) {
        throw new Error(`Chain ${chainId} not found`);
      }

      const allNodes = this.proofChainManager.getAllChainNodes(chainId);
      const verifiedNodes = allNodes.filter(nodeId => {
        const node = this.proofChainManager.getProofNode(nodeId);
        return node && verificationResult.isValid;
      }).length;

      return {
        chainId,
        isValid: verificationResult.isValid,
        confidence: verificationResult.confidence,
        totalNodes: allNodes.length,
        verifiedNodes,
        failedNodes: allNodes.length - verifiedNodes,
        issues: verificationResult.errors,
        verificationTimeMs: Date.now() - startTime
      };

    } catch (error) {
      return {
        chainId,
        isValid: false,
        confidence: 0,
        totalNodes: 0,
        verifiedNodes: 0,
        failedNodes: 0,
        issues: [`Verification failed: ${error instanceof Error ? error.message : String(error)}`],
        verificationTimeMs: Date.now() - startTime
      };
    }
  }

  /**
   * Traces provenance from start to end
   */
  async traceProvenance(startNodeId: string, endNodeId?: string): Promise<ProvenanceVerificationResult> {
    const startTime = Date.now();

    try {
      if (!this.monitor) {
        throw new Error("Monitoring is not enabled");
      }

      const trace = await this.monitor.traceProvenance(startNodeId, endNodeId);

      return {
        traceId: trace.traceId,
        isValid: trace.isVerified,
        confidence: trace.confidence,
        pathLength: trace.path.length,
        isComplete: trace.isComplete,
        issues: trace.issues,
        verificationTimeMs: Date.now() - startTime
      };

    } catch (error) {
      return {
        traceId: "",
        isValid: false,
        confidence: 0,
        pathLength: 0,
        isComplete: false,
        issues: [`Provenance trace failed: ${error instanceof Error ? error.message : String(error)}`],
        verificationTimeMs: Date.now() - startTime
      };
    }
  }

  /**
   * Generates a compliance report
   */
  async generateComplianceReport(): Promise<ComplianceReport> {
    if (!this.monitor) {
      throw new Error("Monitoring is not enabled");
    }

    return await this.monitor.generateComplianceReport();
  }

  /**
   * Gets all alerts
   */
  getAlerts(): any[] {
    if (!this.monitor) {
      return [];
    }

    return this.monitor.getAlerts();
  }

  /**
   * Gets unresolved alerts
   */
  getUnresolvedAlerts(): any[] {
    if (!this.monitor) {
      return [];
    }

    return this.monitor.getUnresolvedAlerts();
  }

  /**
   * Resolves an alert
   */
  resolveAlert(alertId: string): void {
    if (!this.monitor) {
      throw new Error("Monitoring is not enabled");
    }

    this.monitor.resolveAlert(alertId);
  }

  /**
   * Gets system metrics
   */
  getMetrics(): any {
    return this.metrics.snapshot();
  }

  /**
   * Gets proof chain statistics
   */
  getChainStatistics(): {
    totalChains: number;
    totalNodes: number;
    verifiedChains: number;
    failedChains: number;
    averageChainLength: number;
    averageNodeConfidence: number;
  } {
    const chains = Array.from(this.proofChainManager.getAllProofChains().values());
    const nodes = Array.from(this.proofChainManager.getAllProofNodes().values());

    const totalChains = chains.length;
    const totalNodes = nodes.length;
    const verifiedChains = chains.filter(chain => chain.verificationStatus === "verified").length;
    const failedChains = chains.filter(chain => chain.verificationStatus === "failed").length;
    const averageChainLength = totalChains > 0 ? chains.reduce((sum, chain) => sum + chain.totalNodes, 0) / totalChains : 0;
    const averageNodeConfidence = totalNodes > 0 ? nodes.reduce((sum, node) => sum + 0.9, 0) / totalNodes : 0; // Placeholder

    return {
      totalChains,
      totalNodes,
      verifiedChains,
      failedChains,
      averageChainLength,
      averageNodeConfidence
    };
  }

  /**
   * Starts monitoring
   */
  startMonitoring(): void {
    if (!this.monitor) {
      throw new Error("Monitoring is not enabled");
    }

    this.monitor.startMonitoring();
  }

  /**
   * Stops monitoring
   */
  stopMonitoring(): void {
    if (!this.monitor) {
      throw new Error("Monitoring is not enabled");
    }

    this.monitor.stopMonitoring();
  }

  /**
   * Shuts down the API
   */
  shutdown(): void {
    if (this.monitor) {
      this.monitor.stopMonitoring();
    }
  }
}

// Export convenience functions for common operations
export const createProofChainAPI = (config?: Partial<ProofChainAPIConfig>) => {
  return new ProofChainAPI(config);
};

export const withProof = async <T, R>(
  api: ProofChainAPI,
  operation: string,
  input: T,
  operationFn: (input: T) => Promise<R> | R,
  options: {
    type?: "transform" | "compute";
    invariants?: string[];
    parentProofs?: string[];
  } = {}
): Promise<OperationResult<R>> => {
  if (options.type === "compute") {
    return await api.compute(operation, input, operationFn, options);
  } else {
    return await api.transformData(operation, input, operationFn, options);
  }
};

export const verifyChain = async (api: ProofChainAPI, chainId: string): Promise<ChainVerificationResult> => {
  return await api.verifyChain(chainId);
};

export const traceProvenance = async (api: ProofChainAPI, startNodeId: string, endNodeId?: string): Promise<ProvenanceVerificationResult> => {
  return await api.traceProvenance(startNodeId, endNodeId);
};

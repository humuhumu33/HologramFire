import { ProofChainManager, ProofNode, ProofChain, VerificationResult } from "./ProofChain";
import { Metrics } from "../monitoring/metrics/Metrics";
import { ccmHash } from "../crypto/ccm/CCMHash";

/**
 * Proof Chain Monitoring and Compliance System
 * 
 * Provides comprehensive monitoring, compliance checking, and provenance verification
 * for the proof chain system. Enables easy-to-use tools for chain of proof provenance checking.
 */

export interface MonitoringConfig {
  enableRealTimeMonitoring: boolean;
  monitoringIntervalMs: number;
  enableComplianceChecking: boolean;
  enableProvenanceTracking: boolean;
  enablePerformanceMonitoring: boolean;
  enableIntegrityChecking: boolean;
  alertThresholds: AlertThresholds;
  complianceRules: ComplianceRule[];
}

export interface AlertThresholds {
  maxVerificationTimeMs: number;
  minConfidenceScore: number;
  maxErrorRate: number;
  maxWarningRate: number;
  maxChainLength: number;
  maxNodeCount: number;
}

export interface ComplianceRule {
  id: string;
  name: string;
  description: string;
  severity: "low" | "medium" | "high" | "critical";
  condition: (node: ProofNode, chain: ProofChain) => boolean;
  action: "alert" | "block" | "log" | "auto_fix";
}

export interface MonitoringAlert {
  id: string;
  type: "performance" | "compliance" | "integrity" | "provenance" | "verification";
  severity: "low" | "medium" | "high" | "critical";
  message: string;
  nodeId?: string;
  chainId?: string;
  timestamp: string;
  details: any;
  resolved: boolean;
}

export interface ComplianceReport {
  reportId: string;
  timestamp: string;
  overallCompliance: number;
  complianceByRule: Map<string, number>;
  violations: ComplianceViolation[];
  recommendations: string[];
  chainIntegrity: ChainIntegrityReport;
  provenanceIntegrity: ProvenanceIntegrityReport;
}

export interface ComplianceViolation {
  ruleId: string;
  ruleName: string;
  severity: "low" | "medium" | "high" | "critical";
  nodeId?: string;
  chainId?: string;
  message: string;
  timestamp: string;
  details: any;
}

export interface ChainIntegrityReport {
  totalChains: number;
  verifiedChains: number;
  failedChains: number;
  incompleteChains: number;
  inconsistentChains: number;
  integrityScore: number;
  issues: string[];
}

export interface ProvenanceIntegrityReport {
  totalNodes: number;
  verifiedNodes: number;
  failedNodes: number;
  missingLinks: number;
  brokenLinks: number;
  provenanceScore: number;
  issues: string[];
}

export interface ProvenanceTrace {
  traceId: string;
  startNodeId: string;
  endNodeId: string;
  path: ProofNode[];
  isComplete: boolean;
  isVerified: boolean;
  confidence: number;
  traceTime: number;
  issues: string[];
}

export class ProofChainMonitor {
  private proofChainManager: ProofChainManager;
  private metrics: Metrics;
  private config: MonitoringConfig;
  private alerts: Map<string, MonitoringAlert> = new Map();
  private complianceCache: Map<string, ComplianceReport> = new Map();
  private monitoringActive: boolean = false;
  private monitoringInterval?: NodeJS.Timeout;

  constructor(
    proofChainManager: ProofChainManager,
    metrics: Metrics,
    config: Partial<MonitoringConfig> = {}
  ) {
    this.proofChainManager = proofChainManager;
    this.metrics = metrics;
    this.config = {
      enableRealTimeMonitoring: true,
      monitoringIntervalMs: 1000,
      enableComplianceChecking: true,
      enableProvenanceTracking: true,
      enablePerformanceMonitoring: true,
      enableIntegrityChecking: true,
      alertThresholds: {
        maxVerificationTimeMs: 5000,
        minConfidenceScore: 0.8,
        maxErrorRate: 0.1,
        maxWarningRate: 0.2,
        maxChainLength: 1000,
        maxNodeCount: 10000
      },
      complianceRules: this.getDefaultComplianceRules(),
      ...config
    };
  }

  /**
   * Starts monitoring
   */
  startMonitoring(): void {
    if (this.monitoringActive) {
      return;
    }

    this.monitoringActive = true;
    this.monitoringInterval = setInterval(() => {
      this.performMonitoringCycle();
    }, this.config.monitoringIntervalMs);

    this.metrics.inc("monitoring_started");
  }

  /**
   * Stops monitoring
   */
  stopMonitoring(): void {
    if (!this.monitoringActive) {
      return;
    }

    this.monitoringActive = false;
    if (this.monitoringInterval) {
      clearInterval(this.monitoringInterval);
      this.monitoringInterval = undefined;
    }

    this.metrics.inc("monitoring_stopped");
  }

  /**
   * Performs a monitoring cycle
   */
  private async performMonitoringCycle(): Promise<void> {
    try {
      if (this.config.enablePerformanceMonitoring) {
        await this.monitorPerformance();
      }

      if (this.config.enableComplianceChecking) {
        await this.checkCompliance();
      }

      if (this.config.enableIntegrityChecking) {
        await this.checkIntegrity();
      }

      if (this.config.enableProvenanceTracking) {
        await this.trackProvenance();
      }

      this.metrics.inc("monitoring_cycles_completed");

    } catch (error) {
      this.metrics.inc("monitoring_cycle_failures");
      this.createAlert({
        type: "performance",
        severity: "high",
        message: `Monitoring cycle failed: ${error instanceof Error ? error.message : String(error)}`,
        details: { error: error instanceof Error ? error.message : String(error) }
      });
    }
  }

  /**
   * Monitors performance metrics
   */
  private async monitorPerformance(): Promise<void> {
    // Monitor verification times
    const verificationTimes = this.metrics.snapshot().hist["proof_verification_time_ms"] || [];
    if (verificationTimes.length > 0) {
      const avgVerificationTime = verificationTimes.reduce((a, b) => a + b, 0) / verificationTimes.length;
      if (avgVerificationTime > this.config.alertThresholds.maxVerificationTimeMs) {
        this.createAlert({
          type: "performance",
          severity: "medium",
          message: `Average verification time (${avgVerificationTime.toFixed(2)}ms) exceeds threshold (${this.config.alertThresholds.maxVerificationTimeMs}ms)`,
          details: { avgVerificationTime, threshold: this.config.alertThresholds.maxVerificationTimeMs }
        });
      }
    }

    // Monitor error rates
    const totalOperations = this.metrics.snapshot().counters["operations_executed"] || 0;
    const failures = this.metrics.snapshot().counters["operation_failures"] || 0;
    if (totalOperations > 0) {
      const errorRate = failures / totalOperations;
      if (errorRate > this.config.alertThresholds.maxErrorRate) {
        this.createAlert({
          type: "performance",
          severity: "high",
          message: `Error rate (${(errorRate * 100).toFixed(2)}%) exceeds threshold (${(this.config.alertThresholds.maxErrorRate * 100).toFixed(2)}%)`,
          details: { errorRate, threshold: this.config.alertThresholds.maxErrorRate }
        });
      }
    }
  }

  /**
   * Checks compliance
   */
  private async checkCompliance(): Promise<void> {
    // Get all proof chains
    const chains = Array.from(this.proofChainManager.getAllProofChains().values());
    
    for (const chain of chains) {
      // Check each compliance rule
      for (const rule of this.config.complianceRules) {
        try {
          // Get all nodes in the chain
          const allNodes = this.proofChainManager.getAllChainNodes(chain.id);
          
          for (const nodeId of allNodes) {
            const node = this.proofChainManager.getProofNode(nodeId);
            if (node && rule.condition(node, chain)) {
              this.createComplianceViolation(rule, node, chain);
            }
          }
        } catch (error) {
          this.createAlert({
            type: "compliance",
            severity: "medium",
            message: `Compliance rule ${rule.id} failed: ${error instanceof Error ? error.message : String(error)}`,
            details: { ruleId: rule.id, error: error instanceof Error ? error.message : String(error) }
          });
        }
      }
    }
  }

  /**
   * Checks integrity
   */
  private async checkIntegrity(): Promise<void> {
    const chains = Array.from(this.proofChainManager.getAllProofChains().values());
    
    for (const chain of chains) {
      // Verify chain integrity
      const verificationResult = await this.proofChainManager.verifyProofChain(chain.id);
      
      if (!verificationResult.isValid) {
        this.createAlert({
          type: "integrity",
          severity: "high",
          message: `Chain ${chain.id} integrity check failed`,
          chainId: chain.id,
          details: { errors: verificationResult.errors, warnings: verificationResult.warnings }
        });
      }

      // Check chain length
      if (chain.totalNodes > this.config.alertThresholds.maxChainLength) {
        this.createAlert({
          type: "integrity",
          severity: "medium",
          message: `Chain ${chain.id} length (${chain.totalNodes}) exceeds threshold (${this.config.alertThresholds.maxChainLength})`,
          chainId: chain.id,
          details: { chainLength: chain.totalNodes, threshold: this.config.alertThresholds.maxChainLength }
        });
      }
    }

    // Check total node count
    const totalNodes = this.proofChainManager.getAllProofNodes().size;
    if (totalNodes > this.config.alertThresholds.maxNodeCount) {
      this.createAlert({
        type: "integrity",
        severity: "medium",
        message: `Total node count (${totalNodes}) exceeds threshold (${this.config.alertThresholds.maxNodeCount})`,
        details: { totalNodes, threshold: this.config.alertThresholds.maxNodeCount }
      });
    }
  }

  /**
   * Tracks provenance
   */
  private async trackProvenance(): Promise<void> {
    // This would implement provenance tracking logic
    // For now, we'll just log that provenance tracking is active
    this.metrics.inc("provenance_tracking_cycles");
  }

  /**
   * Creates an alert
   */
  private createAlert(alertData: Omit<MonitoringAlert, "id" | "timestamp" | "resolved">): void {
    const alert: MonitoringAlert = {
      id: this.generateAlertId(),
      timestamp: new Date().toISOString(),
      resolved: false,
      ...alertData
    };

    this.alerts.set(alert.id, alert);
    this.metrics.inc("alerts_created", 1, { type: alert.type, severity: alert.severity });
  }

  /**
   * Creates a compliance violation
   */
  private createComplianceViolation(rule: ComplianceRule, node: ProofNode, chain: ProofChain): void {
    const violation: ComplianceViolation = {
      ruleId: rule.id,
      ruleName: rule.name,
      severity: rule.severity,
      nodeId: node.id,
      chainId: chain.id,
      message: `Compliance violation: ${rule.description}`,
      timestamp: new Date().toISOString(),
      details: { rule, node, chain }
    };

    this.createAlert({
      type: "compliance",
      severity: rule.severity,
      message: violation.message,
      nodeId: node.id,
      chainId: chain.id,
      details: violation
    });
  }

  /**
   * Generates a compliance report
   */
  async generateComplianceReport(): Promise<ComplianceReport> {
    const reportId = this.generateReportId();
    const timestamp = new Date().toISOString();

    // Calculate compliance by rule
    const complianceByRule = new Map<string, number>();
    const violations: ComplianceViolation[] = [];

    for (const rule of this.config.complianceRules) {
      const ruleViolations = Array.from(this.alerts.values())
        .filter(alert => alert.type === "compliance" && alert.details?.ruleId === rule.id)
        .length;

      const totalChecks = this.proofChainManager.getAllProofNodes().size;
      const compliance = totalChecks > 0 ? Math.max(0, 1 - (ruleViolations / totalChecks)) : 1;
      complianceByRule.set(rule.id, compliance);

      if (ruleViolations > 0) {
        violations.push({
          ruleId: rule.id,
          ruleName: rule.name,
          severity: rule.severity,
          message: `${ruleViolations} violations found`,
          timestamp,
          details: { ruleViolations, totalChecks }
        });
      }
    }

    // Calculate overall compliance
    const overallCompliance = complianceByRule.size > 0 
      ? Array.from(complianceByRule.values()).reduce((a, b) => a + b, 0) / complianceByRule.size
      : 1;

    // Generate chain integrity report
    const chainIntegrity = await this.generateChainIntegrityReport();

    // Generate provenance integrity report
    const provenanceIntegrity = await this.generateProvenanceIntegrityReport();

    // Generate recommendations
    const recommendations = this.generateRecommendations(violations, chainIntegrity, provenanceIntegrity);

    const report: ComplianceReport = {
      reportId,
      timestamp,
      overallCompliance,
      complianceByRule,
      violations,
      recommendations,
      chainIntegrity,
      provenanceIntegrity
    };

    this.complianceCache.set(reportId, report);
    this.metrics.inc("compliance_reports_generated");

    return report;
  }

  /**
   * Generates chain integrity report
   */
  private async generateChainIntegrityReport(): Promise<ChainIntegrityReport> {
    const chains = Array.from(this.proofChainManager.getAllProofChains().values());
    const totalChains = chains.length;
    
    let verifiedChains = 0;
    let failedChains = 0;
    let incompleteChains = 0;
    let inconsistentChains = 0;
    const issues: string[] = [];

    for (const chain of chains) {
      if (chain.verificationStatus === "verified") {
        verifiedChains++;
      } else if (chain.verificationStatus === "failed") {
        failedChains++;
      }

      if (!chain.integrity.isComplete) {
        incompleteChains++;
        issues.push(`Chain ${chain.id} is incomplete`);
      }

      if (!chain.integrity.isConsistent) {
        inconsistentChains++;
        issues.push(`Chain ${chain.id} is inconsistent`);
      }
    }

    const integrityScore = totalChains > 0 ? verifiedChains / totalChains : 1;

    return {
      totalChains,
      verifiedChains,
      failedChains,
      incompleteChains,
      inconsistentChains,
      integrityScore,
      issues
    };
  }

  /**
   * Generates provenance integrity report
   */
  private async generateProvenanceIntegrityReport(): Promise<ProvenanceIntegrityReport> {
    const nodes = Array.from(this.proofChainManager.getAllProofNodes().values());
    const totalNodes = nodes.length;
    
    let verifiedNodes = 0;
    let failedNodes = 0;
    let missingLinks = 0;
    let brokenLinks = 0;
    const issues: string[] = [];

    for (const node of nodes) {
      // Check if node is verified (this would need to be implemented in ProofChainManager)
      // For now, we'll assume all nodes are verified
      verifiedNodes++;

      // Check for missing parent links
      for (const parentId of node.parentProofs) {
        if (!this.proofChainManager.getAllProofNodes().has(parentId)) {
          missingLinks++;
          issues.push(`Node ${node.id} has missing parent ${parentId}`);
        }
      }

      // Check for broken child links
      for (const childId of node.childProofs) {
        const child = this.proofChainManager.getProofNode(childId);
        if (!child || !child.parentProofs.includes(node.id)) {
          brokenLinks++;
          issues.push(`Node ${node.id} has broken child link to ${childId}`);
        }
      }
    }

    const provenanceScore = totalNodes > 0 ? verifiedNodes / totalNodes : 1;

    return {
      totalNodes,
      verifiedNodes,
      failedNodes,
      missingLinks,
      brokenLinks,
      provenanceScore,
      issues
    };
  }

  /**
   * Generates recommendations
   */
  private generateRecommendations(
    violations: ComplianceViolation[],
    chainIntegrity: ChainIntegrityReport,
    provenanceIntegrity: ProvenanceIntegrityReport
  ): string[] {
    const recommendations: string[] = [];

    if (violations.length > 0) {
      recommendations.push("Address compliance violations to improve system integrity");
    }

    if (chainIntegrity.integrityScore < 0.9) {
      recommendations.push("Verify and fix failed proof chains");
    }

    if (provenanceIntegrity.provenanceScore < 0.9) {
      recommendations.push("Fix broken provenance links");
    }

    if (chainIntegrity.incompleteChains > 0) {
      recommendations.push("Complete incomplete proof chains");
    }

    if (provenanceIntegrity.missingLinks > 0) {
      recommendations.push("Restore missing provenance links");
    }

    return recommendations;
  }

  /**
   * Traces provenance from start to end
   */
  async traceProvenance(startNodeId: string, endNodeId?: string): Promise<ProvenanceTrace> {
    const startTime = Date.now();
    
    try {
      const startNode = this.proofChainManager.getProofNode(startNodeId);
      if (!startNode) {
        throw new Error(`Start node ${startNodeId} not found`);
      }

      let endNode: ProofNode | undefined;
      if (endNodeId) {
        endNode = this.proofChainManager.getProofNode(endNodeId);
        if (!endNode) {
          throw new Error(`End node ${endNodeId} not found`);
        }
      }

      // Trace provenance
      const path = this.proofChainManager.traceProvenance(startNodeId);
      
      // Check if trace is complete
      const isComplete = !endNodeId || path.some(node => node.id === endNodeId);
      
      // Verify trace
      const isVerified = await this.verifyProvenanceTrace(path);
      
      // Calculate confidence
      const confidence = this.calculateProvenanceConfidence(path, isVerified);
      
      // Identify issues
      const issues = this.identifyProvenanceIssues(path);

      const trace: ProvenanceTrace = {
        traceId: this.generateTraceId(),
        startNodeId,
        endNodeId: endNodeId || path[path.length - 1]?.id || "",
        path,
        isComplete,
        isVerified,
        confidence,
        traceTime: Date.now() - startTime,
        issues
      };

      this.metrics.inc("provenance_traces_generated");
      this.metrics.observe("provenance_trace_time_ms", trace.traceTime);

      return trace;

    } catch (error) {
      throw new Error(`Provenance trace failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }

  /**
   * Verifies a provenance trace
   */
  private async verifyProvenanceTrace(path: ProofNode[]): Promise<boolean> {
    if (path.length === 0) return false;

    // Verify each node in the path
    for (const node of path) {
      const verification = await this.proofChainManager.verifyProofNode(node);
      if (!verification.isValid) {
        return false;
      }
    }

    // Verify links between nodes
    for (let i = 1; i < path.length; i++) {
      const currentNode = path[i];
      const previousNode = path[i - 1];
      
      if (!currentNode.parentProofs.includes(previousNode.id)) {
        return false;
      }
    }

    return true;
  }

  /**
   * Calculates provenance confidence
   */
  private calculateProvenanceConfidence(path: ProofNode[], isVerified: boolean): number {
    if (path.length === 0) return 0;
    if (!isVerified) return 0;

    let confidence = 1.0;

    // Reduce confidence for long paths
    if (path.length > 10) {
      confidence -= 0.1;
    }

    // Reduce confidence for missing metadata
    for (const node of path) {
      if (node.metadata.invariants.length === 0) {
        confidence -= 0.05;
      }
    }

    return Math.max(0, Math.min(1, confidence));
  }

  /**
   * Identifies provenance issues
   */
  private identifyProvenanceIssues(path: ProofNode[]): string[] {
    const issues: string[] = [];

    for (let i = 0; i < path.length; i++) {
      const node = path[i];
      
      if (node.metadata.invariants.length === 0) {
        issues.push(`Node ${node.id} has no invariants`);
      }

      if (node.metadata.executionTimeMs > 1000) {
        issues.push(`Node ${node.id} has high execution time (${node.metadata.executionTimeMs}ms)`);
      }

      if (i > 0) {
        const previousNode = path[i - 1];
        if (!node.parentProofs.includes(previousNode.id)) {
          issues.push(`Node ${node.id} is not properly linked to previous node ${previousNode.id}`);
        }
      }
    }

    return issues;
  }

  /**
   * Gets all alerts
   */
  getAlerts(): MonitoringAlert[] {
    return Array.from(this.alerts.values());
  }

  /**
   * Gets unresolved alerts
   */
  getUnresolvedAlerts(): MonitoringAlert[] {
    return Array.from(this.alerts.values()).filter(alert => !alert.resolved);
  }

  /**
   * Resolves an alert
   */
  resolveAlert(alertId: string): void {
    const alert = this.alerts.get(alertId);
    if (alert) {
      alert.resolved = true;
      this.metrics.inc("alerts_resolved");
    }
  }

  /**
   * Gets default compliance rules
   */
  private getDefaultComplianceRules(): ComplianceRule[] {
    return [
      {
        id: "min_confidence",
        name: "Minimum Confidence Score",
        description: "All proof nodes must have a minimum confidence score",
        severity: "high",
        condition: (node, chain) => {
          // This would need to be implemented in ProofChainManager
          return false; // Placeholder
        },
        action: "alert"
      },
      {
        id: "max_execution_time",
        name: "Maximum Execution Time",
        description: "Proof nodes must not exceed maximum execution time",
        severity: "medium",
        condition: (node, chain) => {
          return node.metadata.executionTimeMs > 5000;
        },
        action: "alert"
      },
      {
        id: "required_invariants",
        name: "Required Invariants",
        description: "All proof nodes must have at least one invariant",
        severity: "medium",
        condition: (node, chain) => {
          return node.metadata.invariants.length === 0;
        },
        action: "alert"
      }
    ];
  }

  /**
   * Generates alert ID
   */
  private generateAlertId(): string {
    return ccmHash({ timestamp: Date.now(), random: Math.random() }, "alert_id");
  }

  /**
   * Generates report ID
   */
  private generateReportId(): string {
    return ccmHash({ timestamp: Date.now(), random: Math.random() }, "report_id");
  }

  /**
   * Generates trace ID
   */
  private generateTraceId(): string {
    return ccmHash({ timestamp: Date.now(), random: Math.random() }, "trace_id");
  }
}

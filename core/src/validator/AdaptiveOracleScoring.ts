import { Metrics } from "../monitoring/metrics/Metrics";
import { ccmHash } from "../crypto/ccm/CCMHash";

export interface ScoringComponent {
  name: string;
  weight: number;
  score: number;
  history: number[];
  trend: "improving" | "stable" | "declining";
}

export interface ScoringResult {
  overallScore: number;
  components: ScoringComponent[];
  recommendations: string[];
  confidence: number;
  holographicFingerprint: string;
}

export interface AdaptiveScoringResult {
  overallScore: number;
  components: ScoringComponent[];
  recommendations: string[];
  confidence: number;
  threshold: number;
  recommendation: string;
  adaptive_factors: any;
  holographic_correspondence: any;
}

export interface EnvironmentalFactors {
  temperature: number;
  humidity: number;
  systemLoad: number;
  networkLatency: number;
  memoryPressure: number;
  cpuUtilization: number;
  energyEfficiency: number;
}

export interface ScoringContext {
  moduleType: string;
  complexity: "low" | "medium" | "high";
  criticality: "low" | "medium" | "high";
  performance: PerformanceMetrics;
}

export interface PerformanceMetrics {
  responseTime: number;
  throughput: number;
  accuracy: number;
  stability: number;
}

export class AdaptiveOracleScoring {
  private metrics: Metrics;
  private componentWeights: Map<string, number> = new Map();

  constructor() {
    this.metrics = new Metrics();
    this.initializeDefaultWeights();
  }

  private initializeDefaultWeights(): void {
    this.componentWeights.set("holographic_correspondence", 0.3);
    this.componentWeights.set("resonance_classification", 0.2);
    this.componentWeights.set("cycle_conservation", 0.2);
    this.componentWeights.set("page_conservation", 0.15);
    this.componentWeights.set("witness_required", 0.15);
  }

  calculateScore(
    componentScores: Map<string, number>,
    context: ScoringContext
  ): ScoringResult {
    const startTime = Date.now();
    
    try {
      const components: ScoringComponent[] = [];
      let weightedSum = 0;
      let totalWeight = 0;
      
      for (const [componentName, score] of componentScores) {
        const weight = this.componentWeights.get(componentName) || 0.1;
        const component: ScoringComponent = {
          name: componentName,
          weight,
          score,
          history: [],
          trend: "stable"
        };
        
        components.push(component);
        weightedSum += score * weight;
        totalWeight += weight;
      }
      
      const overallScore = totalWeight > 0 ? weightedSum / totalWeight : 0;
      const confidence = 0.8;
      const recommendations: string[] = [];
      const holographicFingerprint = ccmHash({ components, context }, "adaptive.scoring.fingerprint");
      
      const executionTime = Date.now() - startTime;
      this.metrics.observe("scoring_calculation_time_ms", executionTime);
      this.metrics.inc("scores_calculated", 1);
      
      return {
        overallScore,
        components,
        recommendations,
        confidence,
        holographicFingerprint
      };
      
    } catch (error) {
      this.metrics.inc("scoring_calculation_errors", 1);
      throw new Error(`Scoring calculation failed: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
}
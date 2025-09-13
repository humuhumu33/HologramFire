import { Metrics } from "../metrics/Metrics";
import { evaluateRules, AlertRule, Alert } from "../alerts/Rules";
import { ccmHash } from "../../crypto/ccm/CCMHash";

/** xorshift32 deterministic RNG */
function* xorshift32(seed = 0xC0FFEE) {
  let x = seed >>> 0;
  while (true) {
    x ^= x << 13; x >>>= 0;
    x ^= x >>> 17; x >>>= 0;
    x ^= x << 5;  x >>>= 0;
    yield x >>> 0;
  }
}

export interface AdaptiveChaosPlan {
  iterations: number;
  baseViolationRate: number; // 0..1
  seed?: number;
  adaptationWindow: number; // iterations to consider for adaptation
  minViolationRate: number; // minimum violation rate
  maxViolationRate: number; // maximum violation rate
  adaptationFactor: number; // how aggressively to adapt (0..1)
  targetResilience: number; // target system resilience score (0..1)
}

export interface FailurePattern {
  type: 'holographic_correspondence' | 'cycle_conservation' | 'page_conservation' | 'resonance_classification';
  intensity: number; // 0..1
  duration: number; // iterations
  recoveryTime: number; // iterations to full recovery
}

export interface SystemResilienceMetrics {
  recoveryTime: number;
  failureTolerance: number;
  adaptationSpeed: number;
  stabilityScore: number;
  holographic_correspondence: string;
}

export interface AdaptiveChaosResult {
  alerts: Alert[];
  resilienceMetrics: SystemResilienceMetrics;
  appliedPatterns: FailurePattern[];
  adaptationHistory: Array<{
    iteration: number;
    violationRate: number;
    resilienceScore: number;
    adaptationReason: string;
  }>;
}

export class AdaptiveChaosEngine {
  private metrics: Metrics;
  private rules: AlertRule[];
  private plan: AdaptiveChaosPlan;
  private currentViolationRate: number;
  private adaptationHistory: Array<{
    iteration: number;
    violationRate: number;
    resilienceScore: number;
    adaptationReason: string;
  }> = [];
  private appliedPatterns: FailurePattern[] = [];
  private systemState: {
    lastFailureTime: number;
    consecutiveFailures: number;
    recoveryProgress: number;
    resilienceScore: number;
  } = {
    lastFailureTime: 0,
    consecutiveFailures: 0,
    recoveryProgress: 1.0,
    resilienceScore: 1.0
  };

  constructor(metrics: Metrics, rules: AlertRule[], plan: AdaptiveChaosPlan) {
    this.metrics = metrics;
    this.rules = rules;
    this.plan = plan;
    this.currentViolationRate = plan.baseViolationRate;
  }

  /**
   * Runs adaptive chaos engineering with dynamic failure injection
   */
  runAdaptiveChaos(): AdaptiveChaosResult {
    const rng = xorshift32(this.plan.seed ?? 0xDEADBEEF);
    const startTime = Date.now();

    for (let i = 0; i < this.plan.iterations; i++) {
      // Calculate current system resilience
      const resilienceScore = this.calculateSystemResilience(i);
      
      // Adapt violation rate based on system behavior
      this.adaptViolationRate(i, resilienceScore);
      
      // Generate failure pattern based on current state
      const failurePattern = this.generateFailurePattern(i, resilienceScore);
      
      // Apply failure injection
      this.applyFailureInjection(i, failurePattern, rng);
      
      // Update system state
      this.updateSystemState(i, failurePattern);
      
      // Record adaptation decision
      this.recordAdaptation(i, resilienceScore);
    }

    const alerts = evaluateRules(this.metrics, this.rules);
    const resilienceMetrics = this.calculateFinalResilienceMetrics(startTime);

    return {
      alerts,
      resilienceMetrics,
      appliedPatterns: this.appliedPatterns,
      adaptationHistory: this.adaptationHistory
    };
  }

  /**
   * Calculates current system resilience based on metrics
   */
  private calculateSystemResilience(iteration: number): number {
    const metrics = this.metrics.snapshot();
    
    // Calculate recovery time (time since last failure)
    const timeSinceLastFailure = iteration - this.systemState.lastFailureTime;
    const recoveryTimeScore = Math.min(1.0, timeSinceLastFailure / 10); // Normalize to 0-1
    
    // Calculate failure tolerance (how well system handles consecutive failures)
    const failureToleranceScore = Math.max(0, 1.0 - (this.systemState.consecutiveFailures * 0.1));
    
    // Calculate adaptation speed (how quickly system recovers)
    const adaptationSpeedScore = this.systemState.recoveryProgress;
    
    // Calculate stability score based on violation patterns
    const violationCount = metrics.violations || 0;
    const totalTicks = metrics.counters?.ok_ticks || 1;
    const stabilityScore = Math.max(0, 1.0 - (violationCount / totalTicks));
    
    // Weighted combination of resilience factors
    const resilienceScore = (
      recoveryTimeScore * 0.3 +
      failureToleranceScore * 0.3 +
      adaptationSpeedScore * 0.2 +
      stabilityScore * 0.2
    );

    this.systemState.resilienceScore = resilienceScore;
    return resilienceScore;
  }

  /**
   * Adapts violation rate based on system resilience
   */
  private adaptViolationRate(iteration: number, resilienceScore: number): void {
    const targetResilience = this.plan.targetResilience;
    const adaptationFactor = this.plan.adaptationFactor;
    
    // If system is too resilient, increase challenge
    if (resilienceScore > targetResilience + 0.1) {
      this.currentViolationRate = Math.min(
        this.plan.maxViolationRate,
        this.currentViolationRate + (adaptationFactor * 0.1)
      );
    }
    // If system is struggling, reduce challenge
    else if (resilienceScore < targetResilience - 0.1) {
      this.currentViolationRate = Math.max(
        this.plan.minViolationRate,
        this.currentViolationRate - (adaptationFactor * 0.1)
      );
    }
    
    // Gradual convergence to target
    const convergenceFactor = 0.01;
    const rateDiff = this.currentViolationRate - this.plan.baseViolationRate;
    this.currentViolationRate -= rateDiff * convergenceFactor;
    
    // Ensure bounds
    this.currentViolationRate = Math.max(
      this.plan.minViolationRate,
      Math.min(this.plan.maxViolationRate, this.currentViolationRate)
    );
  }

  /**
   * Generates failure pattern based on current system state
   */
  private generateFailurePattern(iteration: number, resilienceScore: number): FailurePattern {
    const failureTypes: FailurePattern['type'][] = [
      'holographic_correspondence',
      'cycle_conservation', 
      'page_conservation',
      'resonance_classification'
    ];
    
    // Select failure type based on system state
    const typeIndex = Math.floor(resilienceScore * failureTypes.length) % failureTypes.length;
    const type = failureTypes[typeIndex];
    
    // Calculate intensity based on resilience (lower resilience = higher intensity)
    const intensity = Math.max(0.1, 1.0 - resilienceScore);
    
    // Calculate duration based on system recovery capability
    const duration = Math.max(1, Math.floor(5 * (1.0 - resilienceScore)));
    
    // Calculate recovery time based on system adaptation speed
    const recoveryTime = Math.max(1, Math.floor(10 * (1.0 - this.systemState.recoveryProgress)));
    
    const pattern: FailurePattern = {
      type,
      intensity,
      duration,
      recoveryTime
    };
    
    this.appliedPatterns.push(pattern);
    return pattern;
  }

  /**
   * Applies failure injection based on current pattern
   */
  private applyFailureInjection(iteration: number, pattern: FailurePattern, rng: Generator<number, void, unknown>): void {
    const r = (rng.next().value as number) / 0xffffffff;
    const effectiveViolationRate = this.currentViolationRate * pattern.intensity;
    
    if (r < effectiveViolationRate) {
      // Inject failure
      this.metrics.recordViolation(pattern.type, {
        iteration,
        pattern: pattern.type,
        intensity: pattern.intensity,
        seed: this.plan.seed ?? 0xDEADBEEF,
        holographic_correspondence: ccmHash({
          type: 'chaos_failure',
          iteration,
          pattern: pattern.type,
          intensity: pattern.intensity
        }, 'chaos_engine')
      });
      
      this.systemState.consecutiveFailures++;
      this.systemState.lastFailureTime = iteration;
      this.systemState.recoveryProgress = Math.max(0, this.systemState.recoveryProgress - 0.1);
    } else {
      // System operating normally
      this.metrics.inc("ok_ticks", 1);
      
      // Gradually improve recovery progress
      this.systemState.recoveryProgress = Math.min(1.0, this.systemState.recoveryProgress + 0.05);
      
      // Reset consecutive failures if we've been stable
      if (iteration - this.systemState.lastFailureTime > 5) {
        this.systemState.consecutiveFailures = 0;
      }
    }
  }

  /**
   * Updates system state based on applied failure pattern
   */
  private updateSystemState(iteration: number, pattern: FailurePattern): void {
    // Update recovery progress based on pattern duration
    if (pattern.duration > 0) {
      this.systemState.recoveryProgress = Math.max(
        0,
        this.systemState.recoveryProgress - (0.1 / pattern.duration)
      );
    }
  }

  /**
   * Records adaptation decision for analysis
   */
  private recordAdaptation(iteration: number, resilienceScore: number): void {
    if (iteration % this.plan.adaptationWindow === 0) {
      const adaptationReason = this.getAdaptationReason(resilienceScore);
      
      this.adaptationHistory.push({
        iteration,
        violationRate: this.currentViolationRate,
        resilienceScore,
        adaptationReason
      });
    }
  }

  /**
   * Gets human-readable reason for adaptation
   */
  private getAdaptationReason(resilienceScore: number): string {
    const target = this.plan.targetResilience;
    
    if (resilienceScore > target + 0.1) {
      return `System too resilient (${resilienceScore.toFixed(3)} > ${target.toFixed(3)}), increasing challenge`;
    } else if (resilienceScore < target - 0.1) {
      return `System struggling (${resilienceScore.toFixed(3)} < ${target.toFixed(3)}), reducing challenge`;
    } else {
      return `System stable (${resilienceScore.toFixed(3)} ≈ ${target.toFixed(3)}), maintaining challenge`;
    }
  }

  /**
   * Calculates final resilience metrics
   */
  private calculateFinalResilienceMetrics(startTime: number): SystemResilienceMetrics {
    const endTime = Date.now();
    const totalTime = endTime - startTime;
    
    // Calculate average recovery time
    const recoveryTimes = this.adaptationHistory
      .filter(h => h.resilienceScore < 0.8)
      .map(h => h.iteration);
    const avgRecoveryTime = recoveryTimes.length > 0 
      ? recoveryTimes.reduce((a, b) => a + b, 0) / recoveryTimes.length 
      : 0;
    
    // Calculate failure tolerance
    const failureTolerance = Math.max(0, 1.0 - (this.systemState.consecutiveFailures * 0.1));
    
    // Calculate adaptation speed
    const adaptationSpeed = this.systemState.recoveryProgress;
    
    // Calculate stability score
    const metrics = this.metrics.snapshot();
    const violationCount = metrics.violations || 0;
    const totalTicks = metrics.counters?.ok_ticks || 1;
    const stabilityScore = Math.max(0, 1.0 - (violationCount / totalTicks));
    
    return {
      recoveryTime: avgRecoveryTime,
      failureTolerance,
      adaptationSpeed,
      stabilityScore,
      holographic_correspondence: ccmHash({
        recoveryTime: avgRecoveryTime,
        failureTolerance,
        adaptationSpeed,
        stabilityScore,
        totalTime,
        iterations: this.plan.iterations
      }, 'adaptive_chaos')
    };
  }
}

/**
 * Enhanced chaos engineering with adaptive failure injection
 */
export function runAdaptiveChaos(
  metrics: Metrics, 
  rules: AlertRule[], 
  plan: AdaptiveChaosPlan
): AdaptiveChaosResult {
  const engine = new AdaptiveChaosEngine(metrics, rules, plan);
  return engine.runAdaptiveChaos();
}

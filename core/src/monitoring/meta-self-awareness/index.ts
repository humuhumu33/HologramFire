/**
 * Oculus - Meta Self-Awareness Layer
 * 
 * Ultra-efficient overlay witness system for monitoring and optimizing
 * latency, compute requirements, and energy use across the entire system.
 */

export { Oculus } from './Oculus';
export { OculusOverlay } from './OculusOverlay';
export { OculusIntegration } from './OculusIntegration';

// Export types
export type {
  MetaAwarenessConfig,
  SystemMetrics,
  OptimizationDecision,
  MetaAwarenessResult
} from './Oculus';

export type {
  OverlayConfig,
  OverlayWitness,
  OverlayResult
} from './OculusOverlay';

export type {
  IntegrationConfig,
  SystemIntegrationResult,
  OptimizationRecommendation
} from './OculusIntegration';

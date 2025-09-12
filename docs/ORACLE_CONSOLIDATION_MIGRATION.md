# Oracle Consolidation Migration Guide

## Overview

The hologram oracle system has been consolidated from multiple separate implementations into a single **Master Hologram Oracle** that preserves all key features while eliminating duplications.

## What Changed

### Before (Multiple Oracle Implementations)
- `HologramOracle` - Base oracle with core validation
- `EnhancedHologramOracle` - Enhanced validation with adaptive scoring
- `MLEnhancedHologramOracle` - ML optimization and prediction
- `StrictHolographicCoherenceOracle` - Real-time monitoring and strict validation
- `DevelopmentOracle` - Development-focused validation
- `OracleMiddleware` - Middleware for validating new code

### After (Single Master Oracle)
- `MasterHologramOracle` - Unified oracle with mode-based operation
- `MasterOracleCLI` - Single CLI tool with mode selection

## Migration Guide

### For Code Using Oracle Classes

#### Old Usage:
```typescript
import { HologramOracle } from './HologramOracle';
import { EnhancedHologramOracle } from './EnhancedHologramOracle';
import { MLEnhancedHologramOracle } from './MLEnhancedHologramOracle';

const oracle = new HologramOracle();
const result = oracle.validateModule('path/to/module.json');
```

#### New Usage:
```typescript
import { MasterHologramOracle, OracleMode } from './MasterHologramOracle';

// Base mode (equivalent to old HologramOracle)
const baseMode: OracleMode = { type: 'base', config: {} };
const oracle = new MasterHologramOracle(baseMode);
const result = await oracle.validate('path/to/module.json');

// Enhanced mode (equivalent to old EnhancedHologramOracle)
const enhancedMode: OracleMode = { 
  type: 'enhanced', 
  config: { 
    enableAdaptiveScoring: true,
    enablePerformanceCalibration: true 
  } 
};
const enhancedOracle = new MasterHologramOracle(enhancedMode);

// ML-enhanced mode (equivalent to old MLEnhancedHologramOracle)
const mlMode: OracleMode = { 
  type: 'ml-enhanced', 
  config: { 
    enableMLOptimization: true,
    enableMLPerformancePrediction: true 
  } 
};
const mlOracle = new MasterHologramOracle(mlMode);
```

### For CLI Usage

#### Old Commands:
```bash
# Multiple separate CLI tools
npm run validate:oracle:enhanced
npm run validate:oracle:ml
npm run validate:oracle:strict
npm run dev:oracle
```

#### New Commands:
```bash
# Single unified CLI with mode selection
npm run oracle:enhanced --input modules/example.json
npm run oracle:ml --input modules/example.json
npm run oracle:strict --input modules/example.json
npm run oracle:dev --input src/

# Or use the master CLI directly
npm run oracle --mode enhanced --input modules/example.json
npm run oracle --mode ml-enhanced --input modules/example.json
npm run oracle --mode strict --input modules/example.json
npm run oracle --mode development --input src/
```

### Mode Equivalencies

| Old Implementation | New Mode | Key Features |
|-------------------|----------|--------------|
| `HologramOracle` | `base` | Core holographic validation |
| `EnhancedHologramOracle` | `enhanced` | Adaptive scoring, performance calibration, invariant verification |
| `MLEnhancedHologramOracle` | `ml-enhanced` | ML optimization, prediction, anomaly detection, pattern recognition |
| `StrictHolographicCoherenceOracle` | `strict` | Real-time monitoring, strict coherence checking, trend analysis |
| `DevelopmentOracle` | `development` | Real-time feedback, suggestions, quick fixes |
| `OracleMiddleware` | `middleware` | Middleware validation for new code additions |

## Configuration

### Mode-Specific Configuration

Each mode can be configured with specific options:

```typescript
const config: Partial<MasterOracleConfig> = {
  // Base configuration
  threshold: 0.95,
  maxViolations: 10,
  
  // Enhanced features
  enableAdaptiveScoring: true,
  enablePerformanceCalibration: true,
  enableInvariantVerification: true,
  
  // ML features
  enableMLOptimization: true,
  enableMLPerformancePrediction: true,
  enableMLAnomalyDetection: true,
  enableMLPatternRecognition: true,
  
  // Strict monitoring features
  enableRealTimeMonitoring: true,
  monitoringIntervalMs: 1000,
  coherenceThreshold: 0.95,
  
  // Development features
  enableRealTimeFeedback: true,
  enableValidationCache: true
};

const mode: OracleMode = { type: 'ml-enhanced', config };
const oracle = new MasterHologramOracle(mode);
```

### Configuration Files

You can also use configuration files:

```json
{
  "threshold": 0.95,
  "enableAdaptiveScoring": true,
  "enableMLOptimization": true,
  "enableRealTimeMonitoring": false,
  "monitoringIntervalMs": 1000
}
```

```bash
npm run oracle --mode enhanced --config config.json --input modules/example.json
```

## API Changes

### Method Signatures

#### Old:
```typescript
// Different methods for different oracles
oracle.validateModule(path: string): OracleResult
oracle.validateBlueprint(path: string): OracleResult
oracle.validateHologramFunction(code: string, name: string): OracleResult
```

#### New:
```typescript
// Single unified method
oracle.validate(input: string | any, context?: any): Promise<MasterOracleResult>
```

### Result Structure

The new `MasterOracleResult` includes all features from the old implementations:

```typescript
interface MasterOracleResult {
  // Base result
  ok: boolean;
  oracle_score: number;
  violations: OracleViolation[];
  holographic_fingerprint: string;
  
  // Enhanced features (when enabled)
  invariantVerifications?: InvariantVerificationResult[];
  adaptiveScoring?: AdaptiveScoringResult;
  calibrationState?: CalibrationState;
  
  // ML features (when enabled)
  mlOptimization?: MLOptimizationResult;
  mlPerformancePrediction?: MLPredictionResult;
  mlAnomalyDetection?: AnomalyDetectionResult;
  mlHolographicPatterns?: HolographicPatternResult[];
  mlConfidence?: number;
  mlRecommendations?: string[];
  
  // Strict monitoring features (when enabled)
  realTimeMetrics?: RealTimeCoherenceMetrics;
  holographicCorrespondence?: HolographicCorrespondenceMetrics;
  resonanceClassification?: ResonanceClassificationMetrics;
  cycleConservation?: CycleConservationMetrics;
  pageConservation?: PageConservationMetrics;
  coherenceScore?: number;
  violationTrends?: ViolationTrend[];
  
  // Development features (when enabled)
  suggestions?: string[];
  quickFixes?: string[];
  
  // Common metadata
  execution_time_ms: number;
  timestamp: number;
  mode: OracleMode['type'];
}
```

## Benefits of Consolidation

1. **Single Source of Truth**: One oracle implementation instead of multiple overlapping ones
2. **Consistent API**: Unified interface across all oracle functionality
3. **Mode-Based Operation**: Choose the right level of validation for your needs
4. **Reduced Maintenance**: Single codebase to maintain instead of multiple implementations
5. **Better Performance**: Shared components and optimized execution paths
6. **Easier Testing**: Single test suite instead of multiple separate ones
7. **Simplified CLI**: One tool instead of multiple CLI applications

## Backward Compatibility

The old oracle classes are still available but deprecated. They will be removed in a future version. Please migrate to the new `MasterHologramOracle` as soon as possible.

## Testing

Test the new master oracle with:

```bash
# Test different modes
npm run oracle:base --input modules/example-good.json
npm run oracle:enhanced --input modules/example-good.json
npm run oracle:ml --input modules/example-good.json
npm run oracle:strict --input modules/example-good.json

# Test with verbose output
npm run oracle:verbose --mode enhanced --input modules/example-good.json

# Test watch mode
npm run oracle:watch --mode development --input src/
```

## Support

If you encounter any issues during migration, please:

1. Check this migration guide
2. Review the new API documentation
3. Test with the new CLI tools
4. Report any issues or missing features

The master oracle preserves all functionality from the original implementations while providing a cleaner, more maintainable architecture.

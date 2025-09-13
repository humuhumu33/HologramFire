# Proof Chain System

A comprehensive proof generation, verification, and provenance tracking system for all computing and data transformation operations in the hologram system. Provides atomic traceability from start to end with easy-to-use monitoring and compliance tools.

## Features

- **Atomic Traceability**: Every operation generates a proof that can be traced back to its origin
- **Chain of Proof Verification**: Complete verification of proof chains with confidence scoring
- **Data Transformation Proofs**: Specialized proof generation for data transformation operations
- **Computation Proofs**: Specialized proof generation for computational operations
- **Monitoring & Compliance**: Real-time monitoring with compliance checking and alerting
- **Provenance Tracking**: Complete provenance tracing from any point back to the origin
- **Easy-to-Use API**: Simple, intuitive interface for developers
- **CLI Tools**: Command-line interface for operations and monitoring

## Quick Start

### Basic Usage

```typescript
import { createProofChainAPI } from './proof-chain';

// Create API instance
const api = createProofChainAPI({
  enableMonitoring: true,
  enableCompliance: true,
  enableProvenance: true
});

// Execute a data transformation with proof
const result = await api.transformData(
  "double_values",
  [1, 2, 3, 4, 5],
  (input) => input.map(x => x * 2),
  {
    transformationType: "map",
    invariants: ["all_outputs_even", "output_length_equals_input"]
  }
);

console.log("Result:", result.result);
console.log("Proof Node ID:", result.proofNodeId);
console.log("Verification Status:", result.verificationStatus);
console.log("Confidence:", result.confidence);
```

### Computation with Proof

```typescript
// Execute a computation with proof
const result = await api.compute(
  "fibonacci_calculation",
  10,
  (n) => {
    if (n <= 1) return n;
    let a = 0, b = 1;
    for (let i = 2; i <= n; i++) {
      const temp = a + b;
      a = b;
      b = temp;
    }
    return b;
  },
  {
    computationType: "calculation",
    algorithm: "iterative_fibonacci",
    invariants: ["fibonacci_property", "positive_result"]
  }
);
```

### Chaining Operations

```typescript
// Chain multiple operations together
const operations = [
  {
    type: "transform",
    operation: "normalize_data",
    transformFn: (input) => {
      const sum = input.reduce((a, b) => a + b, 0);
      return input.map(x => x / sum);
    },
    options: { invariants: ["sum_equals_one"] }
  },
  {
    type: "compute",
    operation: "calculate_entropy",
    computeFn: (input) => -input.reduce((sum, p) => sum + (p * Math.log2(p)), 0),
    options: { invariants: ["entropy_non_negative"] }
  }
];

const results = await api.chainOperations(operations, [0.1, 0.2, 0.3, 0.4]);
```

## API Reference

### ProofChainAPI

The main API class for all proof chain operations.

#### Constructor

```typescript
const api = new ProofChainAPI(config?: Partial<ProofChainAPIConfig>);
```

#### Methods

##### `transformData<T, R>(operation, input, transformFn, options?)`

Executes a data transformation with proof generation.

**Parameters:**
- `operation: string` - Name of the operation
- `input: T` - Input data
- `transformFn: (input: T) => Promise<R> | R` - Transformation function
- `options?: object` - Optional configuration

**Returns:** `Promise<OperationResult<R>>`

##### `compute<T, R>(operation, input, computeFn, options?)`

Executes a computation with proof generation.

**Parameters:**
- `operation: string` - Name of the operation
- `input: T` - Input data
- `computeFn: (input: T) => Promise<R> | R` - Computation function
- `options?: object` - Optional configuration

**Returns:** `Promise<OperationResult<R>>`

##### `chainOperations<T>(operations, initialInput)`

Chains multiple operations together.

**Parameters:**
- `operations: Array<Operation>` - Array of operations to chain
- `initialInput: T` - Initial input data

**Returns:** `Promise<OperationResult<any>[]>`

##### `verifyChain(chainId)`

Verifies a proof chain.

**Parameters:**
- `chainId: string` - ID of the chain to verify

**Returns:** `Promise<ChainVerificationResult>`

##### `traceProvenance(startNodeId, endNodeId?)`

Traces provenance from start to end.

**Parameters:**
- `startNodeId: string` - Starting node ID
- `endNodeId?: string` - Optional ending node ID

**Returns:** `Promise<ProvenanceVerificationResult>`

##### `generateComplianceReport()`

Generates a compliance report.

**Returns:** `Promise<ComplianceReport>`

##### `getAlerts()`

Gets all alerts.

**Returns:** `MonitoringAlert[]`

##### `getUnresolvedAlerts()`

Gets unresolved alerts.

**Returns:** `MonitoringAlert[]`

##### `resolveAlert(alertId)`

Resolves an alert.

**Parameters:**
- `alertId: string` - ID of the alert to resolve

##### `getMetrics()`

Gets system metrics.

**Returns:** `TelemetrySnapshot`

##### `getChainStatistics()`

Gets proof chain statistics.

**Returns:** `ChainStatistics`

## CLI Usage

The proof chain system includes a comprehensive CLI tool for operations and monitoring.

### Installation

```bash
npm install -g proof-chain-cli
```

### Basic Commands

```bash
# Execute a data transformation
proof-chain transform "double" "[1,2,3]" "input.map(x => x * 2)"

# Execute a computation
proof-chain compute "square" "5" "input * input"

# Verify a proof chain
proof-chain verify "chain-123"

# Trace provenance
proof-chain trace "node-456" "node-789"

# Generate compliance report
proof-chain compliance

# Get alerts
proof-chain alerts --unresolved

# Get system metrics
proof-chain metrics

# Get chain statistics
proof-chain statistics
```

### CLI Options

- `--format <format>` - Output format (json, table, yaml) [default: json]
- `--config <file>` - Configuration file
- `--verbose, -v` - Verbose output
- `--quiet, -q` - Quiet mode
- `--help, -h` - Show help

### Script Execution

You can execute multiple commands from a script file:

```json
[
  {
    "action": "transform",
    "args": {
      "operation": "normalize",
      "input": "[1,2,3,4,5]",
      "transformFn": "input.map(x => x / 15)"
    }
  },
  {
    "action": "compute",
    "args": {
      "operation": "entropy",
      "input": "result",
      "computeFn": "-input.reduce((sum, p) => sum + (p * Math.log2(p)), 0)"
    }
  }
]
```

```bash
proof-chain script operations.json
```

## Monitoring and Compliance

### Real-time Monitoring

The system provides real-time monitoring of:
- Performance metrics
- Compliance violations
- Chain integrity
- Provenance tracking

### Compliance Rules

Default compliance rules include:
- Minimum confidence score requirements
- Maximum execution time limits
- Required invariants validation
- Data integrity checks

### Alerts

The system generates alerts for:
- Performance issues
- Compliance violations
- Integrity failures
- Provenance problems

### Compliance Reports

Compliance reports include:
- Overall compliance score
- Compliance by rule
- Violations and recommendations
- Chain integrity status
- Provenance integrity status

## Architecture

### Core Components

1. **ProofChainManager** - Core proof chain infrastructure
2. **DataTransformationProofSystem** - Data transformation proof generation
3. **ComputationProofSystem** - Computation proof generation
4. **ProofChainMonitor** - Monitoring and compliance system
5. **ProofChainAPI** - Easy-to-use API interface

### Proof Structure

Each proof node contains:
- Unique ID
- Operation details
- Input/output hashes
- Proof and witness
- Metadata and invariants
- Parent/child relationships

### Chain Structure

Proof chains maintain:
- Root and leaf proofs
- Complete node hierarchy
- Chain integrity verification
- Verification status

## Integration

### With Existing Hologram Operations

```typescript
// Integrate with existing hologram operations
const hologramResult = await api.compute(
  "holographic_correspondence",
  inputData,
  existingHologramFunction,
  {
    computationType: "analysis",
    algorithm: "holographic_analysis",
    invariants: ["holographic_correspondence", "resonance_classification"]
  }
);
```

### With Monitoring Systems

```typescript
// Start monitoring
api.startMonitoring();

// Get real-time metrics
const metrics = api.getMetrics();

// Generate compliance report
const report = await api.generateComplianceReport();
```

## Best Practices

### 1. Always Include Invariants

```typescript
const result = await api.transformData(
  "operation",
  input,
  transformFn,
  {
    invariants: ["output_length_equals_input", "all_outputs_positive"]
  }
);
```

### 2. Use Appropriate Operation Types

```typescript
// For data transformations
transformationType: "map" | "filter" | "reduce" | "aggregate" | "normalize"

// For computations
computationType: "algorithm" | "calculation" | "optimization" | "simulation"
```

### 3. Chain Related Operations

```typescript
// Chain related operations for better traceability
const results = await api.chainOperations([
  { type: "transform", operation: "step1", transformFn: step1Fn },
  { type: "compute", operation: "step2", computeFn: step2Fn },
  { type: "transform", operation: "step3", transformFn: step3Fn }
], initialInput);
```

### 4. Monitor and Verify

```typescript
// Always verify chains
const verification = await api.verifyChain(result.chainId);

// Trace provenance when needed
const trace = await api.traceProvenance(startNodeId, endNodeId);
```

### 5. Handle Errors Gracefully

```typescript
try {
  const result = await api.compute("operation", input, computeFn);
  console.log("Success:", result);
} catch (error) {
  console.error("Operation failed:", error);
  // Handle error appropriately
}
```

## Examples

See the `examples/` directory for comprehensive examples including:
- Basic data transformations
- Computations with proof
- Chaining operations
- Verification and provenance
- Monitoring and compliance
- Error handling
- Integration with existing systems

## Configuration

### API Configuration

```typescript
const config: ProofChainAPIConfig = {
  enableMonitoring: true,
  enableCompliance: true,
  enableProvenance: true,
  monitoringConfig: {
    enableRealTimeMonitoring: true,
    monitoringIntervalMs: 1000,
    enableComplianceChecking: true,
    alertThresholds: {
      maxVerificationTimeMs: 5000,
      minConfidenceScore: 0.8,
      maxErrorRate: 0.1
    }
  },
  autoStartMonitoring: true
};
```

### Monitoring Configuration

```typescript
const monitoringConfig: MonitoringConfig = {
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
  }
};
```

## Troubleshooting

### Common Issues

1. **Verification Failures**
   - Check invariants are properly defined
   - Verify input/output data integrity
   - Ensure proper error handling

2. **Performance Issues**
   - Monitor execution times
   - Check resource usage
   - Optimize operations

3. **Compliance Violations**
   - Review compliance rules
   - Check confidence scores
   - Verify data integrity

### Debug Mode

Enable verbose logging for debugging:

```typescript
const api = createProofChainAPI({
  monitoringConfig: {
    enableRealTimeMonitoring: true,
    monitoringIntervalMs: 1000
  }
});

// Enable verbose mode in CLI
proof-chain --verbose <command>
```

## Contributing

1. Follow the existing code style
2. Add comprehensive tests
3. Update documentation
4. Ensure all operations include proper proof generation
5. Maintain backward compatibility

## License

This proof chain system is part of the hologram project and follows the same licensing terms.

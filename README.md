# Hologram

![Hologram Pipeline](https://img.shields.io/badge/Hologram%20Pipeline-FAIL-red?style=flat-square&label=Last%20run&message=Never)

A comprehensive system for holographic data validation, proof generation, and computational verification. Hologram provides atomic traceability, quantum-resistant cryptography, and performance optimization for modern applications requiring high integrity and verifiable computations.

## What This Is

Hologram is a TypeScript-based framework that implements holographic principles for data validation and computational verification. It combines several advanced concepts:

- **Holographic Correspondence**: Each part of the system reflects the whole, ensuring consistency across all operations
- **Proof Chain System**: Complete traceability of all data transformations and computations
- **Quantum-Resistant Cryptography**: Security based on information field conservation rather than computational complexity
- **Oracle Validation**: Reference implementation validation against holographic coherence standards
- **Performance Optimization**: Energy-aware scaling and compressed proof systems

## What It Does

### Core Capabilities

**Data Validation & Verification**
- Validates modules against holographic coherence standards
- Generates cryptographic proofs for all data transformations
- Maintains complete audit trails with atomic traceability
- Provides confidence scoring for verification results

**Proof Generation**
- Creates verifiable proofs for computational operations
- Supports data transformation proofs (map, filter, reduce, aggregate)
- Generates computation proofs (algorithms, calculations, optimizations)
- Maintains proof chains with integrity verification

**Performance Optimization**
- Energy-aware scaling based on system metrics
- Compressed proof systems for reduced storage
- Parallel processing with holographic correspondence
- Adaptive caching with proof-based invalidation

**Multi-Language SDK Support**
- Node.js/TypeScript (primary implementation)
- Python, Go, Rust, and C bindings
- Unified API across all languages
- Cross-platform compatibility

## How It Works

### Architecture Overview

The system is built around several core components:

**Oracle System** (`hologram_generator_mini.py`)
- Reference implementation for holographic validation
- Validates modules against four core invariants:
  - `holographic_correspondence`: Part-whole relationship maintenance
  - `resonance_classification`: Harmonic frequency patterns
  - `cycle_conservation`: Computational energy efficiency
  - `page_conservation`: Memory and storage optimization

**Proof Chain System** (`src/proof-chain/`)
- `ProofChainManager`: Central management of all proof operations
- `DataTransformationProofs`: Specialized proof generation for data operations
- `ComputationProofs`: Proof generation for computational operations
- `ProofChainMonitor`: Real-time monitoring and compliance checking

**Cryptographic Layer** (`src/crypto/`)
- `InformationFieldCrypto`: Quantum-resistant cryptography based on field conservation
- `ConservationBasedAuth`: Authentication through information conservation
- `CCMHash`: Cryptographic hash functions with holographic properties

**Optimization Engine** (`src/optimization/`)
- `HologramPerformanceOptimizer`: Proof-based computation optimization
- `CompressedProofSystem`: Proof compression with integrity preservation
- `EnergyAwareScaling`: Dynamic scaling based on energy consumption

### Validation Process

1. **Module Validation**: Each module is validated against the reference oracle
2. **Invariant Checking**: Verification of holographic correspondence and conservation principles
3. **Proof Generation**: Creation of cryptographic proofs for all operations
4. **Chain Verification**: Integrity verification of the complete proof chain
5. **Performance Monitoring**: Real-time metrics and optimization recommendations

## How to Use It

### Installation

```bash
# Clone the repository
git clone <repository-url>
cd hologram

# Install dependencies
npm install

# Build the project
npm run build
```

### 🚀 Operational Quickstart

**Daily Smoke Test:**
```bash
# Local verification
export IPFS_API=http://127.0.0.1:5001
export GRAPHQL_URL=http://localhost:4000/graphql
python -m pytest -m "phase6_perf or phase8_e2e" -q
python scripts/aggregate_reports.py && python scripts/check_perf_budget.py

# Windows dev quickstart (paths-safe)
```powershell
# one-time (admin): enable long paths + git longpaths
# …or skip if on a managed device
# .\tools\windows_path_hotfix.ps1 -AdminOnly

# daily dev shell (user)
.\tools\windows_dev_shell.ps1

# run pipeline
python -m pytest -m "phase6_perf or phase8_e2e" -q
python scripts/aggregate_reports.py
python scripts/check_perf_budget.py
```

> If you see a path-length error, verify `subst X:` is active and `PYTEST_ADDOPTS` shows short temp paths.

# Windows convenience
.\tools\reports.ps1
.\tools\perf-gate.ps1
```

**Quick Triage:**
```bash
# E2E summary
python scripts/summarize_e2e.py

# Performance check
python scripts/check_perf_budget.py

# Flake report
python scripts/flake_detector.py report

# Status badge
python scripts/status_badge.py markdown
```

**Configuration:**
```bash
# PR (lenient)
export SLO_VERIFY_P95_MS=15 SLO_ENCODE_P95_MS=150 SLO_GQL_P95_MS=150
export GQL_SAMPLES=20 GQL_WARMUP=3 ENC_MB=1

# Main/Nightly (strict)
export SLO_VERIFY_P95_MS=8 SLO_ENCODE_P95_MS=80 SLO_GQL_P95_MS=80
export GQL_SAMPLES=100 GQL_WARMUP=10 ENC_MB=4
```

**Ops Toggles:**
```bash
# Get environment-specific configuration
python scripts/ops_toggles.py pr      # PR configuration
python scripts/ops_toggles.py main    # Main branch configuration
python scripts/ops_toggles.py nightly # Nightly configuration
python scripts/ops_toggles.py dev     # Development configuration
```

### Basic Usage

**Module Validation**
```bash
# Validate a single module
npm run validate:oracle data/modules/example-good.json

# Validate entire blueprint
npm run validate:oracle:blueprint atlas-12288/blueprint/blueprint.json

# Run comprehensive oracle validation
npm run test:oracle
```

**Proof Chain Operations**
```bash
# Execute data transformation with proof
npm run proof-chain:transform

# Perform computation with proof
npm run proof-chain:compute

# Verify proof chain integrity
npm run proof-chain:verify

# Trace provenance
npm run proof-chain:trace
```

**Performance Optimization**
```bash
# Run performance benchmarks
npm run bench

# Generate optimization reports
npm run perf:report

# Monitor system metrics
npm run proof-chain:metrics
```

### Programmatic Usage

**TypeScript/Node.js**
```typescript
import { createProofChainAPI } from './src/proof-chain';
import { HologramOracle } from './src/validator/HologramOracle';

// Create proof chain API
const api = createProofChainAPI({
  enableMonitoring: true,
  enableCompliance: true,
  enableProvenance: true
});

// Execute data transformation with proof
const result = await api.transformData(
  "process_user_data",
  userData,
  (input) => input.map(user => ({ ...user, processed: true })),
  {
    transformationType: "map",
    invariants: ["data_integrity", "holographic_correspondence"]
  }
);

// Validate module against oracle
const oracle = new HologramOracle();
const validation = oracle.validateModule("path/to/module.json");
```

**Python SDK**
```python
import json
import subprocess

# Use the Python SDK (delegates to reference implementation)
result = subprocess.run([
    "python", "-m", "hologram_sdk", "--delegate"
], input=json.dumps({
    "method": "validate_module",
    "params": {"module_path": "data/modules/example-good.json"}
}), capture_output=True, text=True)

validation_result = json.loads(result.stdout)
```

**Go SDK**
```go
package main

import (
    "encoding/json"
    "os/exec"
    "os"
)

func main() {
    cmd := exec.Command("go", "run", "./sdk/go/cmd/hologram")
    cmd.Stdin = os.Stdin
    cmd.Stdout = os.Stdout
    cmd.Run()
}
```

## Practical Application Examples

### Data Pipeline Validation

**Scenario**: ETL pipeline with multiple transformation stages

```typescript
// Validate each stage with holographic proofs
const pipeline = [
  { stage: "extract", operation: "read_database" },
  { stage: "transform", operation: "clean_data" },
  { stage: "load", operation: "write_warehouse" }
];

for (const stage of pipeline) {
  const result = await api.compute(
    stage.operation,
    stageData,
    stageFunction,
    {
      computationType: "algorithm",
      invariants: ["data_integrity", "cycle_conservation"]
    }
  );
  
  console.log(`Stage ${stage.stage}: ${result.verificationStatus}`);
}
```

### Financial Transaction Verification

**Scenario**: High-integrity financial calculations

```typescript
// Calculate portfolio value with verifiable proofs
const portfolioCalculation = await api.compute(
  "calculate_portfolio_value",
  portfolioData,
  (data) => {
    return data.positions.reduce((total, position) => {
      return total + (position.quantity * position.price);
    }, 0);
  },
  {
    computationType: "calculation",
    invariants: ["financial_accuracy", "holographic_correspondence"]
  }
);

// Verify calculation integrity
const verification = await api.verifyProof(portfolioCalculation.proofNodeId);
console.log(`Portfolio value: $${portfolioCalculation.result}`);
console.log(`Verification confidence: ${verification.confidence}`);
```

### Machine Learning Model Validation

**Scenario**: ML model training with proof of correctness

```typescript
// Train model with holographic validation
const modelTraining = await api.compute(
  "train_ml_model",
  trainingData,
  (data) => {
    // Model training logic
    return trainedModel;
  },
  {
    computationType: "algorithm",
    invariants: ["model_convergence", "data_integrity"]
  }
);

// Validate model against oracle standards
const oracle = new HologramOracle();
const modelValidation = oracle.validateModule("models/trained-model.json");
```

### Real-time Monitoring

**Scenario**: System health monitoring with energy optimization

```typescript
// Set up real-time monitoring
const monitor = new ProofChainMonitor(api);

monitor.onAlert((alert) => {
  console.log(`Alert: ${alert.type} - ${alert.message}`);
  
  if (alert.type === 'energy_threshold_exceeded') {
    // Trigger energy optimization
    const optimization = await optimizer.optimizeEnergyConsumption();
    console.log(`Energy savings: ${optimization.energySavings}J`);
  }
});

// Start monitoring
await monitor.startMonitoring();
```

### Cross-Language Integration

**Scenario**: Microservices architecture with multiple languages

```bash
# Node.js service
npm run sdk:smoke:node

# Python service  
npm run sdk:smoke:python

# Go service
npm run sdk:smoke:go

# Rust service
npm run sdk:smoke:rust

# C service
npm run sdk:smoke:c
```

## Development Workflow

### Pre-commit Validation
```bash
# Install pre-commit oracle validation
npm run pre-commit:oracle

# This automatically validates all staged files
# Blocks commits with oracle score < 0.95
```

### Development Mode
```bash
# Start development oracle for real-time feedback
npm run dev:oracle

# Provides instant validation as you type
# Live oracle score updates
# Immediate violation alerts
```

### Testing
```bash
# Run all tests
npm test

# Run oracle-specific tests
npm run test:oracle

# Run proof chain tests
npm run test:proof-chain

# Run performance benchmarks
npm run bench
```

## Configuration

### Oracle Configuration
- **Oracle Score Threshold**: 0.95 (configurable)
- **Critical Violations**: Block all operations
- **Warning Violations**: Logged but don't block
- **Reference Implementation**: `hologram_generator_mini.py`

### Performance Configuration
- **Energy Threshold**: 0.5mJ per operation
- **Latency Threshold**: 100ms
- **Compression Ratio**: 70% target compression
- **Max Concurrency**: 8 parallel operations

### Monitoring Configuration
- **Metrics Collection**: Real-time performance metrics
- **Alert Thresholds**: Configurable for different violation types
- **Compliance Reporting**: Automated compliance checking
- **Provenance Tracing**: Complete operation history

## Contributing

1. All new code must pass oracle validation (score ≥ 0.95)
2. Include required holographic patterns in implementations
3. Maintain proof chain integrity for all operations
4. Follow energy conservation principles
5. Provide comprehensive test coverage

## License

[License information to be added]

## Support

For questions, issues, or contributions, please refer to the project documentation or create an issue in the repository.
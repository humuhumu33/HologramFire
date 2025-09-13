# Hologram Proof Chain Examples

This directory contains comprehensive examples demonstrating the hologram proof chain system for data transformation operations with full provenance tracking.

## Examples Overview

### 1. Data Transformation Proof Chain (`proof-chain-example.ts`)

A complete example showing a 6-step data transformation pipeline with cryptographic proof generation and verification at each step.

**Pipeline Steps:**
1. **Data Validation** - Validate input data structure and content
2. **Data Cleaning** - Remove invalid entries and normalize data
3. **Data Enrichment** - Add computed fields and aggregations
4. **Data Transformation** - Apply business logic transformations
5. **Data Aggregation** - Generate summary statistics
6. **Final Verification** - Verify result integrity and consistency

**Key Features:**
- Complete provenance tracking from raw data to final result
- Cryptographic proof generation at each step
- Chain verification and integrity checking
- Compliance reporting and monitoring
- Performance metrics and confidence scoring

### 2. Proof Chain Visualization (`proof-chain-visualization.md`)

A detailed visual representation of the proof chain structure, showing:
- Proof node relationships and dependencies
- Cryptographic hash chains
- Invariant verification at each step
- Chain integrity verification process
- Compliance and monitoring metrics

## Running the Examples

### Prerequisites

Make sure you have the hologram system built and dependencies installed:

```bash
# Install dependencies
npm install

# Build the system
npm run build
```

### Running the Proof Chain Example

#### Option 1: Using the Node.js runner
```bash
node examples/run-proof-chain-example.js
```

#### Option 2: Using TypeScript directly
```bash
npx ts-node examples/proof-chain-example.ts
```

#### Option 3: Using the built JavaScript
```bash
node build/examples/proof-chain-example.js
```

### Expected Output

The example will produce output similar to:

```
🚀 Starting Data Transformation Proof Chain Example
============================================================

📊 Processing 5 employee records

🔍 Step 1: Data Validation
   ✅ Validation completed - Proof: abc123...
   📈 Confidence: 95.0%

🧹 Step 2: Data Cleaning
   ✅ Cleaning completed - Proof: def456...
   📈 Confidence: 92.0%

✨ Step 3: Data Enrichment
   ✅ Enrichment completed - Proof: ghi789...
   📈 Confidence: 94.0%

🔄 Step 4: Data Transformation
   ✅ Transformation completed - Proof: jkl012...
   📈 Confidence: 93.0%

📊 Step 5: Data Aggregation
   ✅ Aggregation completed - Proof: mno345...
   📈 Confidence: 96.0%

🔐 Step 6: Final Verification
   ✅ Verification completed - Proof: pqr678...
   📈 Confidence: 98.0%

🔗 Verifying Complete Proof Chain
   Chain ID: chain_abc123...
   Total Nodes: 6
   Verified Nodes: 6
   Failed Nodes: 0
   Overall Status: ✅ VALID
   Chain Confidence: 94.7%

🔍 Tracing Provenance
   Trace ID: trace_xyz789...
   Path Length: 6
   Is Complete: ✅
   Trace Confidence: 97.2%

📋 Generating Compliance Report
   Total Operations: 6
   Compliance Score: 100.0%
   Violations: 0
   Warnings: 0

📈 System Statistics
   Total Chains: 1
   Total Nodes: 6
   Verified Chains: 1
   Average Chain Length: 6.0

🎉 Data Transformation Proof Chain Example Completed Successfully!
============================================================

📊 Final Results Summary:
   Total Employees: 4
   Average Salary: $80000.00
   Departments: Engineering, Marketing, Sales
   Data Quality Score: 100.0%

🔗 Complete Proof Chain Visualization
============================================================
Step 1: validate_employee_data
  Proof Node ID: abc123...
  Chain ID: chain_abc123...
  Verification: verified
  Confidence: 95.0%
  Execution Time: 25ms

Step 2: clean_employee_data
  Proof Node ID: def456...
  Chain ID: chain_abc123...
  Verification: verified
  Confidence: 92.0%
  Execution Time: 18ms

... (additional steps)

🔍 Verification Results:
   Chain Valid: ✅
   Chain Confidence: 94.7%
   Provenance Complete: ✅
   Compliance Score: 100.0%
```

## Understanding the Proof Chain

### What is a Proof Chain?

A proof chain is a cryptographically linked sequence of proof nodes, where each node represents a data transformation operation. Each proof node contains:

- **Input Hash**: Cryptographic hash of the input data
- **Output Hash**: Cryptographic hash of the output data
- **Proof**: Cryptographic proof of the transformation
- **Witness**: Witness signature for verification
- **Metadata**: Operation details, invariants, and performance metrics
- **Parent/Child References**: Links to previous and next nodes in the chain

### Key Benefits

1. **Complete Provenance**: Every data transformation is cryptographically proven and traceable
2. **Data Integrity**: Guaranteed consistency and accuracy through cryptographic verification
3. **Audit Trail**: Full traceability from source data to final result
4. **Compliance**: Automated compliance checking and reporting
5. **Performance Monitoring**: Real-time performance metrics and optimization insights
6. **Error Detection**: Automatic detection of data quality issues and inconsistencies
7. **Reproducibility**: All transformations are deterministic and verifiable
8. **Security**: Cryptographic proofs ensure tamper resistance and authenticity

### Proof Chain Structure

```
Raw Data → [Proof Node A] → [Proof Node B] → [Proof Node C] → Final Result
            │                │                │
            └─ Hash A        └─ Hash B        └─ Hash C
            └─ Proof A       └─ Proof B       └─ Proof C
            └─ Witness A     └─ Witness B     └─ Witness C
```

Each proof node is cryptographically linked to its parent and child nodes, creating an immutable chain of evidence for the entire data transformation process.

## Customizing the Example

### Adding New Transformation Steps

To add new transformation steps to the pipeline:

1. Create a new transformation function
2. Add a new step to the `runCompletePipeline()` method
3. Define appropriate invariants for the transformation
4. Link the step to the previous step using `parentProofs`

Example:
```typescript
// Step 7: Custom Transformation
const customResult = await this.api.transformData(
  'custom_transformation',
  previousResult.result,
  this.customTransformFunction,
  {
    transformationType: 'map',
    invariants: [
      'Custom invariant 1',
      'Custom invariant 2'
    ],
    parentProofs: [previousResult.proofNodeId]
  }
);
```

### Modifying Data Structures

To work with different data structures:

1. Update the TypeScript interfaces (`RawDataEntry`, `CleanedDataEntry`, etc.)
2. Modify the transformation functions to work with the new structure
3. Update the validation and verification logic as needed

### Adding Custom Invariants

Invariants are business rules that must be satisfied at each step:

```typescript
invariants: [
  'All records must have valid IDs',
  'Email addresses must be properly formatted',
  'Salary values must be positive',
  'Age must be within reasonable bounds'
]
```

## Integration with Existing Systems

The proof chain system can be integrated into existing data processing pipelines:

1. **Replace existing transformations** with proof-enabled versions
2. **Add proof generation** to existing data processing steps
3. **Implement compliance checking** for regulatory requirements
4. **Add audit trails** for data governance and compliance

## Troubleshooting

### Common Issues

1. **Build Errors**: Make sure the system is built with `npm run build`
2. **Import Errors**: Check that all dependencies are installed with `npm install`
3. **Runtime Errors**: Verify that the proof chain API is properly initialized
4. **Verification Failures**: Check that all invariants are properly defined and satisfied

### Debug Mode

To enable debug logging, set the environment variable:
```bash
DEBUG=hologram:* node examples/run-proof-chain-example.js
```

## Further Reading

- [Proof Chain System Documentation](../src/proof-chain/README.md)
- [API Reference](../src/proof-chain/ProofChainAPI.ts)
- [Data Transformation Proofs](../src/proof-chain/DataTransformationProofs.ts)
- [Computation Proofs](../src/proof-chain/ComputationProofs.ts)
- [Monitoring and Compliance](../src/proof-chain/ProofChainMonitor.ts)

## Contributing

To contribute new examples or improve existing ones:

1. Follow the existing code structure and patterns
2. Include comprehensive documentation and comments
3. Add appropriate error handling and validation
4. Test thoroughly with different data scenarios
5. Update this README with any new examples or features

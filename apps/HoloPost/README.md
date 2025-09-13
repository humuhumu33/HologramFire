# Hologram 12,288 Virtual Infrastructure Demo - HoloPost

A TypeScript CLI demo that proves Hologram's **12,288-cell lattice (48×256)** can act as **virtual infrastructure** for transport, storage, and compute operations, effectively replacing traditional cloud databases.

## 🌟 Overview

This demo showcases how the Hologram lattice can serve as a complete virtual infrastructure stack:

- **Transport**: CTP-96 style O(1) verification + windowed settlement
- **Storage**: Deterministic placement, replicas/erasure coding, witnesses, repair
- **Compute**: Budgeted, pinned near data, receipts

The use case is **HoloPost** — sending a "postcard" message across the lattice, storing it with proofs, and running a kernel that "stamps" it. Every step returns **receipts** that locally verify and **close budgets** for the window.

## 🏗️ Architecture

### Lattice Structure
- **Grid**: 48 rows × 256 columns = 12,288 cells
- **Columns = lanes** (transport QoS shard)
- **Rows ≈ resonance classes / fault domains** for placement
- **Windows**: 100ms default settlement window
- **Placement policy**: At least 3 coords across different rows & columns

### Virtual Infrastructure Components

1. **Transport Layer**
   - Consensus Transport Protocol (CTP) with O(1) verification
   - Windowed settlement with budget enforcement
   - Klein probe verification (192-probe fast check)
   - r96 checksum validation

2. **Storage Layer**
   - Deterministic placement across 48×256 grid
   - Erasure coding (3 data + 2 parity shards)
   - Witness verification for integrity
   - Repair operations for damaged data

3. **Compute Layer**
   - Budgeted kernel execution
   - Co-location with data (pinning)
   - Receipt generation for compute and aggregate operations
   - Witness verification for outputs

## 🚀 Quick Start

### Prerequisites
- Node.js 20+
- npm or yarn

### Installation
```bash
cd apps/HoloPost
npm install
```

### Running the Demo
```bash
# Run the complete demo
npm run demo

# Run individual steps
npm run demo:transport
npm run demo:storage
npm run demo:compute
npm run demo:encoding

# Run performance tests
npm run demo:perf

# Encode/decode text messages
npm run encode "Hello World" r96
npm run decode "SGVsbG8gV29ybGQ=" base64
```

### Testing
```bash
# Run all tests
npm test

# Run tests in watch mode
npm run test:watch

# Run specific test suites
npm test -- --testNamePattern="Transport"
npm test -- --testNamePattern="Storage"
npm test -- --testNamePattern="Compute"
```

## 📁 Project Structure

```
src/
├── adapters/
│   ├── hologram.ts        # SDK adapter (switches mock/real)
│   └── mock.ts            # Deterministic mock implementation
├── steps/
│   ├── 01-transport.ts    # Transport step implementation
│   ├── 02-storage.ts      # Storage step implementation
│   └── 03-compute.ts      # Compute step implementation
├── usecases/
│   └── postcard.ts        # Postcard message system
├── demo.ts                # Main orchestrator
├── testkit.ts             # Test utilities and helpers
└── types.ts               # Core type definitions

tests/
├── setup.ts               # Jest setup
├── verifier.test.ts       # Unit tests for verifier
├── placement.test.ts      # Unit tests for placement
├── postcard.test.ts       # Unit tests for postcard
├── transport.spec.ts      # Transport integration tests
├── storage.spec.ts        # Storage integration tests
├── compute.spec.ts        # Compute integration tests
└── e2e.demo.spec.ts       # End-to-end demo test
```

## 🔧 Configuration

### Environment Variables
- `HOLOGRAM_USE_MOCK`: Set to `'false'` to use real SDK (default: `'true'`)

### Mock vs Real SDK
The demo uses a mock implementation by default. To switch to the real Hologram SDK:

1. Set `HOLOGRAM_USE_MOCK=false`
2. Install the real Hologram SDK package
3. Update imports in `src/adapters/hologram.ts`

## 🚪 Gate System

The HoloPost demo implements a comprehensive **Gate Verification System** that maps every operation to specific gates, providing complete audit trails and explanations. This makes it easy for anyone running the demo to understand what gates are being used and how they work.

### Gate Families

- **G0 - Hologram Oracle**: Core holographic verification and coherence
- **G1 - Core**: Fundamental holographic operations and constraints  
- **G2 - Klein**: Fast frame integrity verification
- **G3 - Logic**: Budget algebra and proof composition
- **G4 - Crypto**: Cryptographic primitives and receipts
- **G5 - Identity**: UOR-ID generation and placement
- **G6 - Transport**: Consensus Transport Protocol
- **G7 - Runtime**: Kernel management and local verification
- **G8 - Persistence**: Object storage and ledger management

### Gate Execution Phases

#### Bootstrap Phase (Startup)
Initializes all gates in the correct order:
1. **G0** - Hologram Oracle initialization
2. **G1** - Core holographic operations
3. **G3** - Logic and budget algebra
4. **G4** - Cryptographic primitives
5. **G5** - Identity and placement
6. **G7** - Runtime and verification

#### Phase A - Transport (A→B, lane 2, O(1) verify)
1. **G6** - CTP handshake establishment
2. **G2** - Klein 192-probe verification
3. **G1 + G3** - Budget conservation and algebra
4. **G4** - Settlement receipt generation
5. **G6** - Fail path handling
6. **G7** - Transport instrumentation

#### Phase B - Storage (PUT/GET/repair on 12,288 lattice)
1. **G5** - UOR-ID computation
2. **G8** - Object layout and placement
3. **G1** - Resonance-based placement
4. **G1** - Budget conservation enforcement
5. **G4** - PUT receipt generation
6. **G8** - Ledger recording
7. **G8 + G4** - Repair with boundary proofs

#### Phase C - Compute (stamp kernel pinned near data)
1. **G7** - VPI registry and kernel spawning
2. **G3 + G1** - Preflight budget validation
3. **G6 + G8** - I/O operations (reused)
4. **G4** - Compute and aggregate receipts
5. **G0** - Final conformance verification

### Gate Audit and Documentation

The demo provides comprehensive gate documentation:

- **Real-time Gate Stamping**: Every operation is stamped with the appropriate gate
- **Audit Trails**: Complete logs of which gates were used when
- **Gate Explanations**: Detailed descriptions of what each gate does
- **Quick Reference**: Phase-by-phase gate usage guide
- **Technical Details**: Algorithm, complexity, security, and performance info

### Understanding Gate Output

When you run the demo, you'll see output like:

```
🔧 [G0] hologram-oracle.spec
   Operation: Initialize holographic oracle
   Purpose: Bootstrap holographic coherence verification
   Description: Loads the blueprint/meta-module, fixed-point self-check
   Timestamp: 2024-01-15T10:30:45.123Z
```

This makes it easy to understand exactly what gates are being used and why.

## 🔐 Text Encoding/Decoding

HoloPost provides comprehensive text encoding and decoding capabilities, allowing users to encode and decode any text message using various encoding schemes supported by the Hologram lattice.

### Available Encoding Schemes

- **Base64**: Standard Base64 encoding (widely supported, URL safe)
- **Hex**: Hexadecimal encoding (simple, human readable, debug friendly)
- **Holographic**: Holographic lattice coordinate encoding (lattice native, fault tolerant, distributed)
- **R96**: R96 checksum-validated encoding (integrity verified, tamper resistant, fast validation)
- **Klein**: Klein probe-validated encoding (probe validated, frame integrity, transport optimized)

### CLI Usage

```bash
# Encode a message
npm run encode "Hello from HoloPost!" r96
npm run encode "Secret message" holographic
npm run encode "Test data" base64

# Decode a message
npm run decode "SGVsbG8gZnJvbSBIb2xvUG9zdCE=" base64
npm run decode "25,205|30,086|16,243|41,009|38,073" holographic
```

### Programmatic Usage

```typescript
import { createEncodedPostcard, decodePostcard } from './usecases/postcard';

// Encode a message
const { postcard, encoded } = createEncodedPostcard(
  'Hello from the Hologram lattice! 🌟',
  'r96'
);

// Decode a postcard
const decoded = decodePostcard(postcard, 'r96');
console.log(`Decoded: ${decoded.decoded}`);
console.log(`Valid: ${decoded.valid}`);
```

### Features

- **Witness Verification**: All encoding schemes include witness verification with r96 checksums and Klein probes
- **Integrity Validation**: Automatic validation during decoding to ensure message integrity
- **Multiple Schemes**: Support for 5 different encoding schemes optimized for different use cases
- **Batch Operations**: Encode/decode multiple messages at once
- **Performance Metrics**: Detailed timing and compression ratio information
- **Gate Integration**: Full integration with the Hologram gate system for audit trails

## 📊 Demo Flow

### Step 1: Transport
1. Create a postcard message
2. Generate witness with r96 checksum
3. Establish CTP connection
4. Send message over lane 2
5. Receive and verify Klein probe
6. Verify r96 checksum
7. Settle window and close budget

### Step 2: Storage
1. Calculate deterministic placement
2. Store postcard with erasure coding
3. Retrieve and verify witness
4. Test repair functionality
5. Validate data integrity

### Step 3: Compute
1. Spawn kernel pinned near input data
2. Execute kernel with budget
3. Generate output with witness
4. Validate compute and aggregate receipts
5. Retrieve processed output

### Step 4: Text Encoding/Decoding
1. Test all available encoding schemes
2. Encode sample messages with witness verification
3. Decode and validate encoded messages
4. Test batch encoding operations
5. Validate round-trip encoding/decoding

## 🧪 Testing

### Unit Tests
- **Verifier**: r96 checksum, Klein probe, budget math
- **Placement**: Deterministic placement across 48×256 grid
- **Postcard**: Message creation, validation, witness generation

### Integration Tests
- **Transport**: CTP handshake, send/receive, settlement, budget enforcement
- **Storage**: Put/get, repair, damage simulation, budget enforcement
- **Compute**: Kernel execution, multiple inputs, different kernel types

### End-to-End Tests
- Complete demo flow validation
- Output consistency checks
- Performance timing validation
- Error handling verification

## 📈 Performance

The demo includes performance testing capabilities:

```bash
npm run demo:perf
```

This runs:
- 100 PUT/GET operations
- 50 transport send/receive cycles
- 25 compute kernel executions

Expected performance (mock implementation):
- Storage: ~1-2ms per operation
- Transport: ~2-3ms per cycle
- Compute: ~5-10ms per kernel

## 🚀 25G Throughput Benchmark

The HoloPost demo includes a comprehensive throughput benchmark suite designed to validate **≥ 25 Gbit/s** sustained transport throughput using the **CTP-96 fast path** over the **48×256 = 12,288** lattice.

### Key Features

- **Lane Parallelism**: Multiple columns for concurrent transport
- **Batching**: Aggregates small payloads to amortize verification overhead
- **Zero-Copy Validation**: Optimized paths for high-throughput scenarios
- **Worker Threading**: Parallel processing across multiple CPU cores
- **Comprehensive Metrics**: Gb/s, frames/s, p50/p99 latency, CPU%, window efficiency

### Quick Start

```bash
# Default 25G benchmark (10s, 32 lanes, 4KB payload)
npm run demo:bench

# High-performance 25G test with real SDK
npm run bench:25g

# Fast mock test (4x speed factor)
npm run bench:mock-fast

# Matrix sweep to find optimal configuration
npm run bench:matrix
```

### Configuration Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `--duration` | 10s | Test duration in seconds |
| `--lanes` | 32 | Number of transport lanes/columns |
| `--payload` | 4096 | Payload size in bytes |
| `--batch` | 16 | Batch size for send operations |
| `--window` | 100ms | Settlement window size |
| `--workers` | 4 | Number of worker threads |
| `--target` | 25 | Target throughput in Gb/s |
| `--aggregate-to` | auto | Aggregate small payloads to this size |

### Performance Tuning

#### What Knobs Matter

1. **Lanes**: More lanes = more parallelism (8-64 recommended)
2. **Payload Size**: Larger payloads = higher efficiency (4KB+ optimal)
3. **Batch Size**: Larger batches = lower overhead (8-32 recommended)
4. **Workers**: Scale with CPU cores (4-8 for most systems)
5. **Window Size**: Balance latency vs efficiency (50-200ms)

#### Aggregation for Small Payloads

For payloads ≤ 2KB, the benchmark automatically aggregates multiple payloads into 4KB frames to:
- Amortize verification overhead
- Reduce per-frame processing costs
- Maintain high throughput even with small messages

Example:
```bash
# Test 1KB payloads aggregated to 4KB frames
npm run demo:bench --payload 1024 --aggregate-to 4096
```

### Real SDK Usage

To test against the real Hologram SDK:

```bash
# Use real SDK instead of mock
HOLOGRAM_USE_MOCK=false npm run demo:bench

# High-performance real SDK test
npm run bench:25g
```

#### Hardware Recommendations

For 25G+ performance with real SDK:
- **NIC**: 25G+ capable network interface
- **CPU**: Multi-core processor with SIMD support
- **Memory**: Sufficient for zero-copy operations
- **OS**: Enable multiple RX/TX queues
- **Tuning**: Set `lanes` to match NIC queue count

### Pass/Fail Criteria

The benchmark **exits with code 0** only if ALL criteria are met:

✅ **Throughput ≥ Target Gb/s** (default: 25)  
✅ **P99 Latency ≤ 2.0ms**  
✅ **Window Efficiency ≥ 99%**  
✅ **Loss Rate ≤ 2%**  

Otherwise **exits with code 1** and shows detailed failure analysis.

### Example Output

```
════════════════════════════════════════════════════════════
CTP-96 Bench — 25G Throughput Validation
════════════════════════════════════════════════════════════

Duration: 10s
Lanes: 32
Payload: 4.0KB
Batch: 16
Window: 100ms
Workers: 4
Target: 25 Gb/s

📊 Results:
Gb/s: 27.3 fps: 829k p50: 0.42ms p99: 1.8ms CPU: 68%

📈 Frame Stats:
Sent: 8.4M Delivered: 8.3M Rejected: 110k
Loss Rate: 1.31%

🪟 Window Settlement:
Windows: 829 closed / 836 total (99.2%)

🛤️  Lane Utilization (top 10):
  L 0: 260k frames
  L 1: 259k frames
  L 2: 258k frames
  ...

🎯 Pass/Fail Criteria:
  ✅ PASS Throughput ≥ Target: 27.3 ≥ 25
  ✅ PASS P99 Latency ≤ 2ms: 1.8 ≤ 2.0
  ✅ PASS Window Efficiency ≥ 99%: 99.2% ≥ 99%
  ✅ PASS Loss Rate ≤ 2%: 1.31% ≤ 2%

🎉 BENCHMARK PASSED - All criteria met!
```

### Advanced Usage

#### Matrix Sweep

Find the optimal configuration automatically:

```bash
npm run bench:matrix
```

Tests combinations of:
- Payload sizes: 1KB, 2KB, 4KB, 8KB
- Lane counts: 8, 16, 32, 64
- Batch sizes: 1, 8, 16, 32
- Aggregation: none, 4KB

#### Custom Configurations

```bash
# High-latency, high-throughput test
npm run demo:bench --duration 30 --lanes 64 --payload 8192 --batch 32

# Low-latency test
npm run demo:bench --window 50 --lanes 16 --payload 2048 --batch 8

# Stress test
npm run demo:bench --duration 60 --lanes 128 --workers 8 --target 50
```

#### Results Export

```bash
# Save results to JSON file
npm run demo:bench --output results.json

# Results are auto-saved to ./bench-results/ directory
```

### Testing

Run the benchmark test suite:

```bash
# Run all benchmark tests
npm run test:bench

# Run specific test categories
npm test -- --testNamePattern="25G"
npm test -- --testNamePattern="Aggregation"
npm test -- --testNamePattern="Budget"
```

### Troubleshooting

#### Common Issues

1. **Low Throughput**: Increase lanes, payload size, or batch size
2. **High Latency**: Reduce window size or increase workers
3. **High Loss Rate**: Increase budget or reduce target throughput
4. **Memory Issues**: Reduce workers or batch size

#### Performance Tips

- Use `--matrix` to find optimal settings for your hardware
- Start with default settings and tune incrementally
- Monitor CPU usage - should be 60-80% for optimal performance
- Ensure sufficient memory for zero-copy operations
- Use real SDK for production performance validation

## 🔍 Key Features

### Budget Enforcement
All operations respect budget constraints:
- Transport: I/O, CPU, memory limits
- Storage: Replication and repair costs
- Compute: Kernel execution budgets

### Receipt Verification
Every operation returns verifiable receipts:
- `ok`: Operation success status
- `windowClosed`: Budget settlement status
- `budgetAfter`: Remaining budget
- `details`: Operation-specific metadata

### Witness Integrity
Data integrity is maintained through:
- r96 checksums (24-hex SHA-256 prefix)
- Klein probe verification (192-probe fast check)
- Deterministic placement validation

### Fault Tolerance
The system demonstrates:
- Cross-fault domain placement
- Erasure coding for data protection
- Repair operations for damaged data
- Budget-based resource management

## 🎯 Acceptance Criteria

✅ **All tests pass**: `npm test` → green  
✅ **Demo runs successfully**: `npm run demo` → complete flow  
✅ **Receipts are closed**: All operations return `windowClosed: true`  
✅ **Lattice structure used**: 48×256 grid coordinates logged  
✅ **Virtual infrastructure demonstrated**: Transport, storage, compute all functional  
✅ **Adapter layer isolated**: Only `hologram.ts` needs changes for real SDK  

## 🚨 Troubleshooting

### Common Issues

1. **Tests failing**: Ensure Node.js 20+ and all dependencies installed
2. **Mock vs Real SDK**: Check `HOLOGRAM_USE_MOCK` environment variable
3. **Performance issues**: Mock implementation is optimized for demo, not production
4. **Memory issues**: Reduce batch sizes in performance tests

### Debug Mode
Set `NODE_ENV=development` for additional logging and debugging information.

## 🔮 Future Enhancements

- Real Hologram SDK integration
- Additional kernel types
- Performance optimization
- Extended fault tolerance testing
- Multi-node simulation

## 📄 License

MIT License - see LICENSE file for details.

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## 📞 Support

For questions or issues:
- Check the troubleshooting section
- Review test outputs for error details
- Ensure all prerequisites are met
- Verify environment configuration

---

**Hologram Virtual Infrastructure Demo** - Proving that a 12,288-cell lattice can replace traditional cloud databases! 🌟

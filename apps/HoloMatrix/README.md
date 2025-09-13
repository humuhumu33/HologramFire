# Hologram Virtual Infra MatMul Demo

A TypeScript CLI demo showcasing **lossless, verifiable streaming matrix multiplication** over Hologram's **12,288-cell lattice (48×256)** with receipts at every layer (transport, storage, compute).

## 🎯 Objective

Implement a comprehensive demonstration of Hologram's virtual infrastructure capabilities with explicit target benchmarks:

- **Initial target**: 2048×2048 block matmul at **≥ 25 Gbit/s** sustained throughput
- **Latency targets**: p50 ≤ 0.6ms, p99 ≤ 1.8ms for transport
- **Window closure**: ≥ 99.5% of windows closed
- **Reject rate**: ≤ 2% for admission/over-budget scenarios

## 🏗️ Architecture

### 12,288 Lattice Mapping

The system operates on a **12,288-cell lattice** organized as:
- **Rows (48)**: Resonance/fault domains for data placement
- **Columns (256)**: Transport lanes for data streaming
- **Total cells**: 48 × 256 = 12,288

### Core Components

1. **Transport Layer (CTP-96)**: O(1) verification with window settlement
2. **Storage Layer**: Deterministic placement with witness verification
3. **Compute Layer**: Pinned kernels with compute receipts
4. **Verification Layer**: R96 hashing and Klein verification

## 🚀 Quick Start

### Prerequisites

- Node.js 18+ 
- TypeScript 5.0+
- npm or yarn

### Installation

```bash
cd apps/HoloMatrix
npm install
```

### Running the Demo

```bash
# Run matrix multiplication demo (default)
npm run demo

# Run benchmark mode
npm run demo:bench

# Run specific steps
npm run demo:transport
npm run demo:storage
npm run demo:compute

# Run with custom parameters
npm run demo:matmul -- --size 1024 --block 64 --lanes 32 --targetGbps 15
```

## 📊 Benchmarks & Acceptance Gates

### Hard Pass/Fail Criteria

The demo enforces strict acceptance gates:

| Metric | Threshold | Description |
|--------|-----------|-------------|
| Throughput | ≥ 25.0 Gbit/s | Sustained throughput |
| Transport p99 | ≤ 1.8 ms | 99th percentile latency |
| Storage p99 | ≤ 3.0 ms | Storage operation latency |
| Compute p99 | ≤ 10.0 ms | Kernel execution latency |
| E2E p99 | ≤ 20.0 ms | End-to-end latency |
| Window closure | ≥ 99.5% | Settlement success rate |
| Reject rate | ≤ 2.0% | Admission control rejects |

### Default Configuration

```typescript
{
  size: 2048,        // Matrix side length
  block: 128,        // Block size (128×128)
  lanes: 64,         // Transport lanes
  payload: 4096,     // Frame size (4KB)
  batch: 16,         // Frames per batch
  workers: 4,        // Worker threads
  window: 100,       // Settlement window (ms)
  targetGbps: 25.0   // Target throughput
}
```

## 🔧 Scalability Knobs

The system exposes CLI flags for scaling:

```bash
--lanes <int>        # Transport lanes (8-128, default 64)
--payload <bytes>    # Frame size (2048-8192, default 4096)
--batch <int>        # Batch size (1-32, default 16)
--workers <int>      # Worker threads (1-16, default 4-8)
--window <ms>        # Settlement window (50-200, default 100)
--size <n>           # Matrix size (2048/8192/16384, default 2048)
--block <n>          # Block size (64/128/256, default 128)
--targetGbps <float> # Target throughput (default 25.0)
```

### Scaling Strategies

- **Higher throughput**: Increase lanes, batch size, workers, payload to 8KB
- **Lower latency**: Shrink critical path, pre-pin buffers, userspace networking
- **Larger matrices**: Raise `--size` to 8192 or 16384

## 🏛️ Gate System

The implementation follows Hologram's gate system with explicit logging:

### Bootstrap Gates
- `G0.hologram-oracle.spec`
- `G0.strict-holographic-coherence-oracle.spec`
- `G1.holography.spec` / `G1.conservation.spec` / `G1.resonance.spec`
- `G3.r96.semiring.spec`
- `G4.receipt.spec`
- `G5.uorid.kat.spec` + `G5.fixtures.spec`
- `G7.vpi.registry.spec`

### Transport Gates (CTP-96)
- Handshake: `G6.ctp.handshake.spec` → `G1.conservation.spec`
- Ingress/Egress: `G2.klein.spec` → `G1.conservation.spec` + `G3.r96.semiring.spec`
- Window settle: `G6.ctp.window.spec` → `G4.receipt.spec`

### Storage Gates
- PUT: `G5.uorid.kat.spec` → `G1.resonance.spec` → `G8.object.spec` → `G4.receipt.spec`
- GET: `G8.object.spec` → `G7.local.verifier.spec`
- REPAIR: `G8.object.spec` → `G4.boundary.spec` → `G8.object.spec` → `G4.receipt.spec`

### Compute Gates
- Register: `G7.vpi.registry.spec`
- Preflight: `G3.r96.semiring.spec` + `G1.conservation.spec`
- Execute: `G4.receipt.spec` (compute + aggregate)

## 🔌 Adapter System

### Real SDK Integration

The system uses the real Hologram SDK for all operations:

```bash
# Run with real SDK
npm run demo
```

### SDK Features

- Real R96 hashing using Hologram SDK
- Actual Klein verification
- Real storage with witness verification
- Production compute kernels
- Full SDK integration

## 📁 Project Structure

```
src/
├── adapters/
│   ├── hologram.ts        # Real SDK adapter
│   └── real-sdk.ts        # Real SDK implementation
├── bench/
│   ├── histogram.ts       # Performance metrics
│   ├── loadgen.ts         # Load generation
│   └── report.ts          # Report generation
├── steps/
│   ├── 01-transport.ts    # CTP-96 transport
│   ├── 02-storage.ts      # Storage operations
│   ├── 03-compute.ts      # Kernel execution
│   ├── 04-bench.ts        # Benchmarking
│   └── 05-matmul.ts       # Matrix multiplication
├── usecases/
│   ├── postcard.ts        # Simple payload demo
│   └── matmul.ts          # Matrix operations
├── testkit.ts             # Test utilities
├── types.ts               # Type definitions
└── demo.ts                # Main orchestrator
```

## 🧪 Testing

### Run Tests

```bash
# Run all tests
npm test

# Run tests in watch mode
npm run test:watch

# Run specific test file
npm test
```

### Test Coverage

- **Unit tests**: Verifier, budget math, placement validation
- **Integration tests**: Transport, storage, compute workflows
- **E2E tests**: Full matrix multiplication pipeline

## 📈 Performance Monitoring

### Live Metrics

The demo provides real-time metrics display:

```
Throughput: 25.8 Gbit/s | Transport p99:1.7ms | Storage p99:2.8ms | 
Compute p99:9.1ms | E2E p99:18ms | Windows closed: 100% | Rejects: 0.8%
```

### Report Generation

- **Console output**: Pretty-printed performance summary
- **JSON export**: Detailed metrics to `./bench-results/`
- **Gate validation**: Pass/fail status for all acceptance criteria

## 🔍 Logging

The system provides detailed logging with gate names:

```
G6.ctp.handshake ✅ peer=node-B
lane=12 frame=4096B G2.klein✅ r96✅ G1/G3 admit✅
window=W42 G6.settle → G4.receipt: closed (frames=128k bytes=512MB)
PUT id=uor:… place→ [(3,41),(19,212),(37,77)] G1/G3 admit✅ G8.write✅ → G4.receipt: closed
spawn matmul-block(3,7) pin row=19 lane=5 preflight G3/G1✅
compute receipt G4: closed; budgetAfter={cpuMs:1, io:0}
aggregate window W42: closed=100%
```

## 🚀 Future Enhancements

### Scalability Roadmap

1. **Higher Throughput**
   - Multi-rail networking (multiple NIC ports)
   - Kernel-bypass I/O (DPDK/RDMA)
   - Larger payload sizes (8KB+)
   - Increased lane count (128+)

2. **Lower Latency**
   - Pre-pinned buffers
   - Userspace networking
   - SmartNIC/FPGA offload for Klein/R96
   - Critical path optimization

3. **Larger Matrices**
   - Support for 8192×8192 and 16384×16384
   - Distributed computation across multiple nodes
   - Advanced load balancing

### Real SDK Integration

To switch to the real Hologram SDK:

1. Update imports in `src/adapters/hologram.ts`
2. Implement real adapter methods
3. Ensure Hologram SDK is properly configured
4. Configure real SDK credentials

## 📚 API Reference

### Core Types

```typescript
interface Budget {
  cpuMs: number;
  io: number;
  mem: number;
}

interface Witness {
  r96: string;
  timestamp: number;
  nodeId: string;
}

interface Receipt {
  id: string;
  closed: boolean;
  timestamp: number;
  gate: string;
  metadata?: Record<string, unknown>;
}
```

### Adapter Interface

```typescript
interface HologramAdapter {
  createVerifier(): Promise<Verifier>;
  createCTP(opts: CTPOptions): Promise<CTP>;
  createStorage(opts: StorageOptions): Promise<Storage>;
  spawnKernel(opts: KernelOptions): Promise<Kernel>;
  uorIdFromBytes(bytes: Buffer): string;
  place(id: string, opts: PlaceOptions): LatticeCoord[];
  capabilities?(): Capabilities;
}
```

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass
5. Submit a pull request

## 📄 License

MIT License - see LICENSE file for details.

## 🆘 Support

For questions or issues:
- Check the test suite for usage examples
- Review the gate system documentation
- Examine the real SDK implementation for reference
- Create an issue with detailed reproduction steps

---

**Built with ❤️ for the Hologram ecosystem**

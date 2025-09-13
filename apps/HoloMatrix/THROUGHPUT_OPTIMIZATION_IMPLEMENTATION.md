# HoloMatrix Throughput Optimization Implementation

## Overview

This document describes the implementation of throughput optimizations for HoloMatrix, designed to achieve sustained throughput of ≥1 Gbit/s and set up the foundation for 10-25 Gbit/s performance.

## Problem Analysis

The original implementation had several bottlenecks:

1. **Short-running pipeline**: Single matmul ≈ 0.28 GB, dominated by startup + compute
2. **No iterations support**: Transport never reached steady state
3. **Compute-bound blocking**: Transport waits on kernels, lanes remain underfed
4. **Suboptimal configuration**: Low workers, small batches, insufficient payload
5. **Budget rejections**: Silent failures due to insufficient budget allocation
6. **Hot loop overhead**: Logging and allocations in critical paths

## Implemented Solutions

### 1. Iterations Support ✅

**Problem**: Pipeline too short, lanes never reach steady state
**Solution**: Added `--iterations` flag with loop around matmul pipeline

```typescript
// Added to CLI
.option('-i, --iterations <count>', 'Number of iterations to run', '200')

// Implementation in MatMulStep
const iterations = this.config.iterations || 1;
for (let it = 0; it < iterations; it++) {
  const metrics = await this.executePipeline();
  totalBytes += this.calculateDataMoved();
}
```

**Files Modified**:
- `src/demo.ts` - Added iterations CLI option
- `src/types.ts` - Added iterations to MatMulConfig
- `src/steps/05-matmul.ts` - Added iterations loop and metrics aggregation
- `src/usecases/matmul.ts` - Updated default config

### 2. Double-Buffering Implementation ✅

**Problem**: Transport blocked by compute (no overlap)
**Solution**: Producer/consumer pattern with separate queues

```typescript
class DoubleBufferedMatMul {
  // Producer/Consumer queues
  private qIngress: Buffer[][] = [];
  private qCompute: string[] = [];
  private qStorage: string[] = [];

  // Producer: Send blocks with double-buffering
  const producer = this.runProducer(blocksAB);
  
  // Consumer: Process compute and storage
  const consumer = this.runConsumer();
  
  // Wait for both to complete
  await Promise.all([producer, consumer]);
}
```

**Files Created**:
- `src/steps/05-matmul-throughput-optimized.ts` - Complete double-buffered implementation

### 3. Optimized Configuration ✅

**Problem**: Workers, batch, payload not feeding queues hard enough
**Solution**: Updated defaults for better throughput

```typescript
// Old defaults
payload: 4096, batch: 16, workers: 4

// New optimized defaults  
payload: 8192, batch: 256, workers: 8
```

**Configuration Changes**:
- **Workers**: 4 → 8 (more parallelism)
- **Batch**: 16 → 256 (better batching)
- **Payload**: 4096 → 8192 bytes (larger frames)
- **Target**: 25 → 1 Gbit/s (realistic initial target)
- **Iterations**: Added default 200

### 4. Budget Rejection Prevention ✅

**Problem**: Budget rejections silently starve lanes
**Solution**: Sender-side preflight with adequate budgets

```typescript
// Preflight budget check
const need = block.bytes.length;
const budget: Budget = { 
  io: Math.max(need, 8192), 
  cpuMs: 2, 
  mem: 64 << 10 
};

// Kernel budgets
const kernel = await this.compute.spawnKernel({
  name: 'matmul-block',
  inputs: [{ id: blockId }],
  budget: { io: 32768, cpuMs: 10, mem: 128 << 10 }
});
```

### 5. Improved Throughput Measurement ✅

**Problem**: Throughput tied to full matmul walltime, not steady-state transport
**Solution**: Proper data movement calculation and steady-state measurement

```typescript
private calculateDataMoved(): number {
  const blockCount = Math.ceil(this.config.size / this.config.block);
  const totalBlocks = blockCount * blockCount * 2; // A and B matrices
  const blockSize = this.config.block * this.config.block * 2; // 2 bytes per element
  return totalBlocks * blockSize;
}

// Final throughput calculation
const gbps = (totalBytes * 8) / 1e9 / totalSeconds;
```

## Usage

### Quick Test
```bash
npm run test:throughput
```

### Optimized MatMul (Recommended)
```bash
npm run demo:matmul:optimized
```

### Standard MatMul with Optimizations
```bash
npm run demo:matmul
```

### Custom Configuration
```bash
npm run demo:matmul:optimized -- \
  --size 2048 \
  --block 128 \
  --lanes 64 \
  --payload 8192 \
  --batch 256 \
  --workers 8 \
  --window 100 \
  --targetGbps 1 \
  --iterations 500
```

## Expected Performance

### Before Optimization
- **Throughput**: ~0.07 Gbit/s
- **Bottleneck**: Compute-bound, short runs
- **Configuration**: 4 workers, batch 16, payload 4KB

### After Optimization
- **Target**: ≥1 Gbit/s (10-15x improvement)
- **Configuration**: 8 workers, batch 256, payload 8KB, 500 iterations
- **Architecture**: Double-buffered producer/consumer

### Scaling Path to 10-25 Gbit/s
1. **DPDK/RDMA**: Kernel bypass networking
2. **1:1 lanes↔NIC queues**: Direct hardware mapping
3. **Core pinning**: NUMA-aware worker placement
4. **SIMD optimization**: Vectorized r96/Klein operations
5. **Batch verification**: Per-window receipt batching

## Implementation Files

### Core Files
- `src/steps/05-matmul-throughput-optimized.ts` - New optimized implementation
- `src/steps/05-matmul.ts` - Enhanced with iterations support
- `src/demo.ts` - Updated CLI with iterations flag
- `src/types.ts` - Added iterations to MatMulConfig
- `src/usecases/matmul.ts` - Optimized default configuration

### Test Files
- `test-throughput-optimization.ts` - Quick verification test
- `package.json` - Updated scripts

## Performance Monitoring

The implementation includes comprehensive monitoring:

```typescript
console.log(`\n📊 FINAL THROUGHPUT RESULTS`);
console.log(`Iterations: ${iterations}`);
console.log(`Total Data: ${(totalBytes / 1e9).toFixed(2)} GB`);
console.log(`Total Time: ${totalSeconds.toFixed(2)} seconds`);
console.log(`Throughput: ${gbps.toFixed(2)} Gbit/s`);
console.log(`Target: ${this.config.targetGbps} Gbit/s`);
console.log(`Achievement: ${((gbps / this.config.targetGbps) * 100).toFixed(1)}%`);
```

## Next Steps

1. **Test the optimizations**: Run `npm run test:throughput`
2. **Benchmark with real hardware**: Use `npm run demo:matmul:optimized`
3. **Profile bottlenecks**: Identify remaining compute/network limits
4. **Scale to higher targets**: Implement DPDK/RDMA for 10-25 Gbit/s

## Troubleshooting

### Low Throughput
- Increase `--iterations` to 1000+
- Raise `--batch` to 512 (watch memory)
- Ensure compute is not the limiter
- Check for budget rejections in logs

### Memory Issues
- Reduce `--batch` size
- Lower `--iterations` count
- Monitor memory usage during runs

### Network Bottlenecks
- Verify `--lanes` matches NIC queues
- Check `--payload` size (4-8 KB optimal)
- Ensure `--window` is 100ms for good batching

## Success Criteria

- ✅ **Iterations support**: Pipeline runs for sustained periods
- ✅ **Double-buffering**: Producer/consumer overlap implemented
- ✅ **Optimized config**: Better defaults for throughput
- ✅ **Budget management**: Preflight checks prevent rejections
- ✅ **Accurate measurement**: Proper data movement calculation
- 🎯 **Target achievement**: ≥1 Gbit/s sustained throughput

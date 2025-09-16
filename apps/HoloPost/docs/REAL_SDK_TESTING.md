# Real SDK Testing Guide for HoloPost

This guide explains how to test HoloPost using the actual Hologram SDK and benchmark against 25G/second throughput targets.

## 🚀 Quick Start

### Prerequisites
- Node.js 20+
- All dependencies installed: `npm install`
- Real Hologram SDK properly configured

### Basic Real SDK Test
```bash
# Run real SDK tests
npm run test:real-sdk

# Run 25G benchmark with real SDK
npm run bench:25g:real
```

## 📊 Available Test Commands

### Real SDK Tests
```bash
# Run real SDK integration tests
npm run test:real-sdk

# Run real SDK tests in watch mode
npm run test:real-sdk:watch

# Run comprehensive real SDK benchmark suite
npm run bench:25g:comprehensive

# Run stress tests with real SDK
npm run bench:25g:stress

# Compare mock vs real SDK performance
npm run bench:25g:compare
```

### Custom Benchmark Runner
```bash
# Basic 25G benchmark
node run-real-sdk-benchmark.js

# High-performance test
node run-real-sdk-benchmark.js --duration 30 --lanes 128 --workers 16

# Comprehensive test suite
node run-real-sdk-benchmark.js --comprehensive

# Stress test
node run-real-sdk-benchmark.js --stress --duration 60

# Compare with mock SDK
node run-real-sdk-benchmark.js --compare
```

## 🧪 Test Categories

### 1. Real SDK Integration Tests
- **File**: `tests/real-sdk-benchmark.spec.ts`
- **Purpose**: Validate real SDK components work correctly
- **Tests**:
  - SDK initialization
  - Basic operations (verifier, CTP, storage, kernel)
  - Witness creation and validation
  - Storage operations (put/get/repair)

### 2. 25G Throughput Benchmark
- **Purpose**: Validate 25G/second throughput target
- **Configuration**:
  - Duration: 15 seconds
  - Lanes: 64
  - Payload: 4KB
  - Workers: 8
  - Target: 25 Gb/s
- **Pass Criteria**:
  - ✅ Throughput ≥ 25 Gb/s
  - ✅ P99 Latency ≤ 2.0ms
  - ✅ Window Efficiency ≥ 99%
  - ✅ Loss Rate ≤ 2%

### 3. Performance Scaling Tests
- **Concurrency Scaling**: Tests with different lane counts and worker threads
- **Payload Scaling**: Tests with different payload sizes (1KB to 64KB)
- **Load Balancing**: Validates load distribution across lanes

### 4. Optimized Throughput Test
- **File**: `src/optimized-throughput-test.ts`
- **Purpose**: High-performance test with advanced optimizations
- **Features**:
  - Worker thread pools
  - Advanced compression
  - Zero-copy operations
  - GPU acceleration simulation
  - Memory optimization

### 5. Stress Testing
- **High Concurrency**: 128 lanes, 16 workers, 50 Gb/s target
- **Memory Pressure**: Large payloads, extended duration
- **Error Recovery**: Budget exhaustion, temporary failures

### 6. Performance Comparison
- **Mock vs Real SDK**: Side-by-side performance comparison
- **Throughput Analysis**: Gb/s, latency, efficiency metrics
- **Resource Usage**: CPU, memory, network utilization

## 🔧 Configuration

### Environment Variables
```bash
# Use real SDK (default: true for mock)
HOLOGRAM_USE_MOCK=false

# SDK configuration
HOLOGRAM_API_ENDPOINT=https://api.hologram.dev
HOLOGRAM_TIMEOUT=30000
HOLOGRAM_RETRIES=3

# Performance tuning
MOCK_SPEED_FACTOR=1  # Only used with mock SDK
```

### Benchmark Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `--duration` | 15s | Test duration in seconds |
| `--lanes` | 64 | Number of transport lanes |
| `--payload` | 4096 | Payload size in bytes |
| `--workers` | 8 | Number of worker threads |
| `--target` | 25 | Target throughput in Gb/s |
| `--batch` | 32 | Batch size for operations |
| `--window` | 100 | Settlement window in ms |

## 📈 Performance Metrics

### Key Metrics Tracked
- **Throughput**: Gb/s achieved
- **Latency**: P50, P99 latency in milliseconds
- **Window Efficiency**: Percentage of windows closed successfully
- **Loss Rate**: Percentage of rejected operations
- **Lane Utilization**: Distribution across transport lanes
- **Resource Usage**: CPU, memory, network utilization

### Performance Targets
- **Primary Target**: 25 Gb/s sustained throughput
- **Latency Target**: P99 ≤ 2.0ms
- **Efficiency Target**: ≥ 99% window closure
- **Loss Target**: ≤ 2% operation rejection

## 🚨 Troubleshooting

### Common Issues

#### 1. SDK Initialization Failures
```bash
# Check SDK configuration
echo $HOLOGRAM_API_ENDPOINT
echo $HOLOGRAM_USE_MOCK

# Verify dependencies
npm list @hologram/sdk
```

#### 2. Low Throughput
- **Increase lanes**: More lanes = more parallelism
- **Increase workers**: Scale with CPU cores
- **Increase payload size**: Larger payloads = higher efficiency
- **Check network**: Ensure sufficient bandwidth

#### 3. High Latency
- **Reduce window size**: Faster settlement
- **Increase workers**: More parallel processing
- **Optimize batch size**: Balance latency vs throughput

#### 4. Memory Issues
- **Reduce workers**: Lower memory usage
- **Reduce batch size**: Smaller memory footprint
- **Check system resources**: Ensure sufficient RAM

### Performance Optimization Tips

#### Hardware Recommendations
- **CPU**: Multi-core processor with SIMD support
- **Memory**: 16GB+ RAM for high concurrency
- **Network**: 25G+ capable network interface
- **Storage**: SSD for better I/O performance

#### Software Optimization
- **Node.js**: Use latest LTS version
- **OS**: Enable multiple RX/TX queues
- **Tuning**: Set lanes to match NIC queue count
- **Monitoring**: Use system monitoring tools

## 📊 Example Output

### Successful 25G Benchmark
```
════════════════════════════════════════════════════════════
CTP-96 Bench — 25G Throughput Validation (Real SDK)
════════════════════════════════════════════════════════════

Duration: 15s
Lanes: 64
Payload: 4.0KB
Batch: 32
Window: 100ms
Workers: 8
Target: 25 Gb/s

📊 Results:
Gb/s: 27.3 fps: 829k p50: 0.42ms p99: 1.8ms CPU: 68%

📈 Frame Stats:
Sent: 8.4M Delivered: 8.3M Rejected: 110k
Loss Rate: 1.31%

🪟 Window Settlement:
Windows: 829 closed / 836 total (99.2%)

🎯 Pass/Fail Criteria:
  ✅ PASS Throughput ≥ Target: 27.3 ≥ 25
  ✅ PASS P99 Latency ≤ 2ms: 1.8 ≤ 2.0
  ✅ PASS Window Efficiency ≥ 99%: 99.2% ≥ 99%
  ✅ PASS Loss Rate ≤ 2%: 1.31% ≤ 2%

🎉 BENCHMARK PASSED - All criteria met!
```

### Performance Comparison
```
📊 Mock vs Real SDK Comparison:
   Real SDK: 12.5 Gb/s, 1.2ms p50
   Mock SDK: 45.2 Gb/s, 0.3ms p50
   Throughput Ratio: 0.28x
   Latency Ratio: 4.0x
```

## 🔍 Advanced Usage

### Custom Test Scenarios
```bash
# Test specific payload sizes
node run-real-sdk-benchmark.js --payload 8192 --lanes 32

# Test high concurrency
node run-real-sdk-benchmark.js --lanes 128 --workers 16 --duration 30

# Test with different targets
node run-real-sdk-benchmark.js --target 50 --duration 20
```

### Continuous Integration
```yaml
# Example CI configuration
- name: Run Real SDK Tests
  run: |
    npm run test:real-sdk
    npm run bench:25g:real
  env:
    HOLOGRAM_USE_MOCK: false
    HOLOGRAM_API_ENDPOINT: ${{ secrets.HOLOGRAM_API_ENDPOINT }}
```

### Monitoring and Alerting
- Set up performance monitoring for CI/CD
- Alert on throughput drops below 20 Gb/s
- Monitor latency increases above 5ms P99
- Track window efficiency below 95%

## 📚 Additional Resources

- [Hologram SDK Documentation](../../libs/sdk/)
- [Performance Optimization Guide](HOLOGRAM_PERFORMANCE_OPTIMIZATION.md)
- [Throughput Optimization README](THROUGHPUT_OPTIMIZATION_README.md)
- [Benchmark Results](./bench-results/)

## 🤝 Contributing

When adding new tests:
1. Follow the existing test structure
2. Include both mock and real SDK variants
3. Add performance assertions
4. Update this documentation
5. Ensure tests pass in CI/CD

## 📞 Support

For issues with real SDK testing:
1. Check the troubleshooting section
2. Review test outputs for error details
3. Verify SDK configuration
4. Check system resources
5. Consult the Hologram SDK documentation

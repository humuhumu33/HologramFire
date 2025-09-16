# Hologram Fire E2E Test Suite

This directory contains comprehensive End-to-End (E2E) tests for the Hologram Fire system, including strict validation tests and performance tests with load generation.

## Test Files

### Core E2E Tests

- **`test_e2e_publish_install.py`** - Basic E2E tests with graceful fallbacks
- **`test_e2e_strict.py`** - Strict E2E tests with no fallbacks (fails fast if anything is missing)
- **`test_e2e_load_integration.py`** - E2E tests with integrated load generation
- **`test_e2e_performance.py`** - Performance-validated E2E tests (requires TypeScript load generator)

### Utilities

- **`run_e2e_suite.py`** - Comprehensive test runner script
- **`_e2e_utils.py`** - Shared utilities for E2E tests

## Quick Start

### 1. Set Environment Variables

```bash
# Required
export IPFS_API=http://127.0.0.1:5001
export GRAPHQL_URL=http://localhost:4000/graphql

# Optional
export GRAPHQL_TOKEN="Bearer <your-token>"
```

### 2. Run All E2E Tests

```bash
# Run the complete test suite
python tests/phase8_e2e/run_e2e_suite.py

# Run with verbose output
python tests/phase8_e2e/run_e2e_suite.py --verbose

# Run specific test types
python tests/phase8_e2e/run_e2e_suite.py --test strict
python tests/phase8_e2e/run_e2e_suite.py --test performance
python tests/phase8_e2e/run_e2e_suite.py --test stress
```

### 3. Run Individual Tests

```bash
# Basic E2E tests (with fallbacks)
python -m pytest tests/phase8_e2e/test_e2e_publish_install.py -v

# Strict E2E tests (no fallbacks)
python -m pytest tests/phase8_e2e/test_e2e_strict.py -v -m strict

# Performance E2E tests
python -m pytest tests/phase8_e2e/test_e2e_load_integration.py -v -m performance
```

## Test Types

### Basic E2E Tests (`test_e2e_publish_install.py`)

- **Purpose**: Validate the complete publish → register → resolve → verify flow
- **Features**: Graceful fallbacks, multiple GraphQL mutation variants
- **Use Case**: General E2E validation with tolerance for schema variations

### Strict E2E Tests (`test_e2e_strict.py`)

- **Purpose**: Enforce strict requirements with no fallbacks
- **Features**: 
  - Requires specific GraphQL mutations (`publishApp`)
  - Validates proof system (merkleRoot, witnesses)
  - Tests tamper detection
  - Validates idempotence
- **Use Case**: Production readiness validation, CI/CD gates

### Performance E2E Tests (`test_e2e_load_integration.py`)

- **Purpose**: Validate system performance under load
- **Features**:
  - Python-based load generator
  - Multi-threaded concurrent operations
  - Performance metrics collection
  - Throughput and latency validation
- **Use Case**: Performance regression testing, capacity planning

### Stress Tests

- **Purpose**: Find system breaking points
- **Features**: Higher load, more lenient thresholds
- **Use Case**: System limits validation, scalability testing

## Performance Test Configuration

### Environment Variables

```bash
# Load test parameters
export E2E_LOAD_DURATION=5          # Test duration in seconds
export E2E_LOAD_WORKERS=4           # Number of concurrent workers
export E2E_LOAD_PAYLOAD=1024        # Payload size in bytes
export E2E_LOAD_OPS_PER_SEC=10      # Operations per second per worker

# Stress test parameters
export E2E_STRESS_DURATION=10       # Stress test duration
export E2E_STRESS_WORKERS=8         # More workers for stress
export E2E_STRESS_PAYLOAD=4096      # Larger payloads
export E2E_STRESS_OPS_PER_SEC=20    # Higher operation rate
```

### Performance Thresholds

#### Load Tests
- **Delivery Rate**: ≥ 80% of sent operations must be delivered
- **Throughput**: Must achieve measurable throughput (> 0.1 Mbps)
- **P99 Latency**: < 5000ms
- **Error Rate**: < 10%

#### Stress Tests
- **Delivery Rate**: ≥ 60% (more lenient)
- **Throughput**: Must achieve some throughput (> 0.05 Mbps)
- **Error Rate**: < 20% (more lenient)

## Test Output

### Event Logging

All tests log events to `reports/e2e/` directory:

- `events.jsonl` - Basic E2E test events
- `performance_events.jsonl` - Performance test events
- `load_events.jsonl` - Load test events
- `stress_events.jsonl` - Stress test events

### Test Reports

Generate comprehensive test reports:

```bash
python tests/phase8_e2e/run_e2e_suite.py --report
```

This creates `reports/e2e_test_report.json` with aggregated results.

## Integration with CI/CD

### GitHub Actions Example

```yaml
name: E2E Tests
on: [push, pull_request]

jobs:
  e2e-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup IPFS
        run: |
          wget https://dist.ipfs.io/go-ipfs/v0.15.0/go-ipfs_v0.15.0_linux-amd64.tar.gz
          tar -xzf go-ipfs_v0.15.0_linux-amd64.tar.gz
          sudo mv go-ipfs/ipfs /usr/local/bin/
          ipfs init
          ipfs daemon &
          sleep 10
      
      - name: Setup GraphQL Server
        run: |
          # Your GraphQL server setup here
          npm start &
          sleep 30
      
      - name: Run E2E Tests
        env:
          IPFS_API: http://127.0.0.1:5001
          GRAPHQL_URL: http://localhost:4000/graphql
        run: |
          python tests/phase8_e2e/run_e2e_suite.py --test strict
```

### Docker Integration

```dockerfile
FROM node:18-alpine

# Install Python and dependencies
RUN apk add --no-cache python3 py3-pip
RUN pip3 install pytest requests

# Copy your application
COPY . /app
WORKDIR /app

# Install dependencies
RUN npm install

# Run E2E tests
CMD ["python3", "tests/phase8_e2e/run_e2e_suite.py"]
```

## Troubleshooting

### Common Issues

1. **IPFS Connection Failed**
   ```
   Error: IPFS_API not set
   ```
   - Ensure IPFS is running: `ipfs daemon`
   - Set `IPFS_API=http://127.0.0.1:5001`

2. **GraphQL Connection Failed**
   ```
   Error: GraphQL error(s): [...]
   ```
   - Ensure GraphQL server is running
   - Check `GRAPHQL_URL` is correct
   - Verify authentication token if required

3. **Performance Tests Failing**
   ```
   Error: Delivery rate 0.50% below 80% threshold
   ```
   - Check system resources (CPU, memory)
   - Reduce load test parameters
   - Check network connectivity

4. **Strict Tests Failing**
   ```
   Error: publishApp failed
   ```
   - Verify GraphQL schema has `publishApp` mutation
   - Check mutation parameters match expected format
   - Ensure all required fields are present

### Debug Mode

Run tests with maximum verbosity:

```bash
python tests/phase8_e2e/run_e2e_suite.py --verbose --test strict
```

### Manual Testing

Test individual components:

```bash
# Test IPFS connectivity
curl -X POST "http://127.0.0.1:5001/api/v0/version"

# Test GraphQL connectivity
curl -X POST "http://localhost:4000/graphql" \
  -H "Content-Type: application/json" \
  -d '{"query": "{ __schema { types { name } } }"}'
```

## Contributing

When adding new E2E tests:

1. Follow the existing patterns in `_e2e_utils.py`
2. Add appropriate markers (`@pytest.mark.phase8_e2e`, `@pytest.mark.performance`)
3. Include comprehensive logging with `_log_event()`
4. Add environment variable configuration
5. Update this README with new test descriptions

## Performance Benchmarks

### Expected Performance (on modern hardware)

- **Basic E2E**: < 5 seconds
- **Strict E2E**: < 3 seconds  
- **Load Test (5s, 4 workers, 1KB)**: 10+ ops/sec, < 100ms P99 latency
- **Stress Test (10s, 8 workers, 4KB)**: 20+ ops/sec, < 500ms P99 latency

### Scaling Guidelines

- **Small systems**: 2-4 workers, 1KB payloads
- **Medium systems**: 4-8 workers, 4KB payloads  
- **Large systems**: 8-16 workers, 16KB+ payloads

Adjust test parameters based on your system capacity and requirements.
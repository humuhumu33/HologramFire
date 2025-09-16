# HoloPost Parallel Processing

This document describes the parallel processing capabilities implemented in HoloPost, including real SDK integration and concurrent operations.

## Overview

HoloPost now supports parallel processing for:
- **Transport Operations**: Concurrent message sending across multiple lanes
- **Storage Operations**: Parallel data storage with replication
- **Compute Operations**: Concurrent kernel execution
- **Postcard Processing**: Parallel postcard handling

## Real SDK Integration

### Configuration

The system automatically switches between mock and real SDK implementations based on the `HOLOGRAM_USE_MOCK` environment variable:

```bash
# Use mock implementation (default)
export HOLOGRAM_USE_MOCK=true

# Use real SDK implementation
export HOLOGRAM_USE_MOCK=false
```

### Real SDK Features

When using the real SDK (`HOLOGRAM_USE_MOCK=false`), the following features are enabled:

- **UOR-ID Generation**: Content-addressed identifiers using the Hologram SDK
- **Witness Generation**: Cryptographic witnesses for data integrity
- **Proof Verification**: C96 arithmetic for budget proofs
- **WebSocket Transport**: Real-time communication via CTP-96
- **Distributed Storage**: Lattice-based data placement and replication

### Environment Variables

```bash
# SDK Configuration
HOLOGRAM_API_ENDPOINT=https://api.hologram.dev
HOLOGRAM_TIMEOUT=30000
HOLOGRAM_RETRIES=3

# Parallel Processing Configuration
HOLOGRAM_MAX_CONCURRENCY=4
HOLOGRAM_TIMEOUT=30000
HOLOGRAM_RETRY_ATTEMPTS=3
HOLOGRAM_RETRY_DELAY=1000
```

## Parallel Processing

### ParallelProcessor Class

The `ParallelProcessor` class provides concurrent execution capabilities:

```typescript
import { createParallelProcessor } from './src/parallel/processor';

const processor = createParallelProcessor({
  maxConcurrency: 4,
  timeout: 30000,
  retryAttempts: 3,
  retryDelay: 1000,
});

await processor.initialize();
```

### Parallel Operations

#### Transport Operations

```typescript
const transportOps = [
  {
    lane: 0,
    payload: Buffer.from('message 1'),
    budget: { io: 50, cpuMs: 25 },
    attach: { r96: 'witness-1', probes: 192 },
  },
  {
    lane: 1,
    payload: Buffer.from('message 2'),
    budget: { io: 50, cpuMs: 25 },
    attach: { r96: 'witness-2', probes: 192 },
  },
];

const results = await processor.parallelTransport(transportOps, ctpConfig);
```

#### Storage Operations

```typescript
const storageOps = [
  {
    id: 'data-1',
    bytes: Buffer.from('content 1'),
    policy: { replication: 3 },
    budget: { io: 100, cpuMs: 50 },
    witness: { r96: 'witness-1', probes: 192, timestamp: Date.now() },
  },
  {
    id: 'data-2',
    bytes: Buffer.from('content 2'),
    policy: { replication: 3 },
    budget: { io: 100, cpuMs: 50 },
    witness: { r96: 'witness-2', probes: 192, timestamp: Date.now() },
  },
];

const results = await processor.parallelStorage(storageOps, latticeConfig);
```

#### Compute Operations

```typescript
const computeOps = [
  {
    name: 'kernel-1',
    inputs: [{ id: 'input-1' }],
    budget: { io: 200, cpuMs: 100 },
    pin: { near: 'input-1', lane: 0 },
  },
  {
    name: 'kernel-2',
    inputs: [{ id: 'input-2' }],
    budget: { io: 200, cpuMs: 100 },
    pin: { near: 'input-2', lane: 1 },
  },
];

const results = await processor.parallelCompute(computeOps, latticeConfig);
```

#### Postcard Processing

```typescript
const postcards = [
  {
    id: 'postcard-1',
    message: 'Hello from parallel processing!',
    from: 'sender-1',
    to: 'recipient-1',
    timestamp: Date.now(),
    bytes: Buffer.from(JSON.stringify({...}), 'utf8'),
  },
  // ... more postcards
];

const results = await processor.parallelPostcards(postcards, latticeConfig);
```

### Performance Monitoring

The parallel processor provides detailed performance statistics:

```typescript
const stats = processor.getStats(results);

console.log(`Total operations: ${stats.total}`);
console.log(`Successful: ${stats.successful}`);
console.log(`Failed: ${stats.failed}`);
console.log(`Average duration: ${stats.averageDuration}ms`);
console.log(`Total duration: ${stats.totalDuration}ms`);
console.log(`Total retries: ${stats.totalRetries}`);
```

### Error Handling

The parallel processor includes robust error handling:

- **Retry Logic**: Automatic retry with exponential backoff
- **Timeout Handling**: Configurable timeouts for operations
- **Graceful Degradation**: Partial success handling
- **Resource Cleanup**: Automatic cleanup of resources

## Usage Examples

### Running the Parallel Demo

```bash
# Run parallel processing demo with mock SDK
npm run demo:parallel

# Run parallel processing demo with real SDK
npm run demo:parallel:real

# Run parallel processing from main demo
npm run demo:parallel:main
```

### Running Tests

```bash
# Run all tests including parallel processing tests
npm test

# Run only parallel processing tests
npm test -- --testNamePattern="Parallel Processing"
```

### Environment Configuration

```bash
# Use real SDK
export HOLOGRAM_USE_MOCK=false

# Configure parallel processing
export HOLOGRAM_MAX_CONCURRENCY=8
export HOLOGRAM_TIMEOUT=60000
export HOLOGRAM_RETRY_ATTEMPTS=5

# Run demo
npm run demo:parallel:real
```

## Architecture

### Components

1. **Real SDK Adapter** (`src/adapters/real-sdk.ts`)
   - Integrates with the actual Hologram SDK
   - Provides UOR-ID generation and witness verification
   - Implements C96 arithmetic for proofs

2. **Parallel Processor** (`src/parallel/processor.ts`)
   - Manages concurrent operations
   - Provides retry logic and error handling
   - Monitors performance and statistics

3. **Parallel Demo** (`src/parallel-demo.ts`)
   - Demonstrates parallel processing capabilities
   - Provides comprehensive testing scenarios
   - Shows performance comparisons

4. **Tests** (`tests/parallel.test.ts`)
   - Comprehensive test coverage
   - Performance validation
   - Error handling verification

### Data Flow

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   Operations    │───▶│ Parallel Processor│───▶│   Results       │
│   (Transport,   │    │                  │    │   (Success/     │
│    Storage,     │    │ - Concurrency    │    │    Failure,     │
│    Compute)     │    │ - Retry Logic    │    │    Statistics)  │
└─────────────────┘    │ - Error Handling │    └─────────────────┘
                       └──────────────────┘
                                │
                                ▼
                       ┌──────────────────┐
                       │   Real SDK       │
                       │                  │
                       │ - UOR-ID Gen     │
                       │ - Witness Verif  │
                       │ - Proof Verif    │
                       └──────────────────┘
```

## Performance Benefits

### Concurrency

- **Transport**: Multiple lanes can be used simultaneously
- **Storage**: Parallel data placement and replication
- **Compute**: Concurrent kernel execution
- **Postcards**: Batch processing of multiple postcards

### Scalability

- **Configurable Concurrency**: Adjust based on system capabilities
- **Resource Management**: Automatic cleanup and resource management
- **Load Balancing**: Distributed operations across lattice cells

### Reliability

- **Retry Logic**: Automatic retry with exponential backoff
- **Error Isolation**: Failed operations don't affect others
- **Graceful Degradation**: Partial success handling

## Future Enhancements

### Planned Features

1. **Dynamic Concurrency**: Automatic adjustment based on system load
2. **Priority Queues**: Operation prioritization
3. **Circuit Breakers**: Automatic failure detection and recovery
4. **Metrics Collection**: Detailed performance metrics
5. **Distributed Processing**: Multi-node parallel processing

### Integration Opportunities

1. **Kubernetes**: Container orchestration integration
2. **Docker**: Container-based parallel processing
3. **Cloud Providers**: AWS, GCP, Azure integration
4. **Monitoring**: Prometheus, Grafana integration

## Troubleshooting

### Common Issues

1. **SDK Connection Failures**
   - Check `HOLOGRAM_API_ENDPOINT` configuration
   - Verify network connectivity
   - Check authentication credentials

2. **Parallel Processing Timeouts**
   - Increase `HOLOGRAM_TIMEOUT` value
   - Reduce `HOLOGRAM_MAX_CONCURRENCY`
   - Check system resources

3. **Memory Issues**
   - Reduce batch sizes
   - Increase system memory
   - Monitor memory usage

### Debug Mode

```bash
# Enable debug logging
export DEBUG=hologram:*

# Run with verbose output
npm run demo:parallel -- --verbose
```

## Contributing

### Development Setup

1. Install dependencies:
   ```bash
   npm install
   ```

2. Run tests:
   ```bash
   npm test
   ```

3. Run parallel demo:
   ```bash
   npm run demo:parallel
   ```

### Code Style

- Use TypeScript for type safety
- Follow existing code patterns
- Add comprehensive tests
- Document new features

### Testing

- Write unit tests for new functionality
- Add integration tests for parallel processing
- Test both mock and real SDK implementations
- Validate performance characteristics

# Hologram E2E Test Suite

This directory contains comprehensive end-to-end tests for the Hologram Docker-compatible API. The tests validate Docker UX compatibility while ensuring Hologram-specific features work correctly.

## Test Categories

### 1. Container Lifecycle (`containers_lifecycle_test.go`)
- **Purpose**: Validates the complete container lifecycle (create, start, logs, inspect, stop, remove)
- **Focus**: Docker API shape compatibility and basic functionality
- **Key Validations**: 
  - Container creation and startup
  - Log streaming
  - Inspect response structure matches Docker
  - Clean shutdown and removal

### 2. Events Stream (`events_test.go`)
- **Purpose**: Tests Docker events API with optional Hologram extensions
- **Focus**: Event streaming compatibility
- **Key Validations**:
  - Events API responds correctly
  - Optional XHologram attributes in verbose mode
  - Event filtering works as expected

### 3. Volumes (`volumes_test.go`)
- **Purpose**: Tests volume management (named volumes and bind mounts)
- **Focus**: Volume API compatibility
- **Key Validations**:
  - Named volume creation and mounting
  - Bind mount support
  - Volume lifecycle management

### 4. Networking (`network_test.go`)
- **Purpose**: Tests network creation and container connectivity
- **Focus**: Network API compatibility and CTP96 driver
- **Key Validations**:
  - Bridge network creation
  - Container network attachment
  - CTP96 driver compatibility (when enabled)

### 5. Enforce Mode (`enforce_test.go`)
- **Purpose**: Tests witness enforcement functionality
- **Focus**: Security and policy enforcement
- **Key Validations**:
  - Invalid witness rejection
  - Valid witness acceptance
  - Proper error messages

### 6. Verbose Mode (`verbose_inspect_test.go`)
- **Purpose**: Tests extended inspect responses with XHologram fields
- **Focus**: Hologram-specific data exposure
- **Key Validations**:
  - XHologram fields in image inspect
  - XHologram fields in container inspect
  - Raw HTTP validation for extended fields

### 7. Parity Tests (`parity_golden_test.go`)
- **Purpose**: Validates API response structure matches Docker
- **Focus**: API compatibility and shape validation
- **Key Validations**:
  - Version endpoint compatibility
  - Container list structure
  - Network list structure
  - Image list structure

### 8. Performance Benchmarks (`bench_start_latency_test.go`)
- **Purpose**: Measures performance characteristics
- **Focus**: Latency and throughput validation
- **Key Metrics**:
  - Container start latency
  - Image pull latency
  - Container inspect latency

## Running Tests

### Prerequisites
- Go 1.21+
- Docker daemon running
- Hologram daemon built and available

### Basic Usage

```bash
# Run all tests in compatibility mode
make e2e

# Run verbose mode tests
make verbose

# Run enforce mode tests
make enforce

# Run race detector tests
make race

# Run performance benchmarks
make bench

# Run all test modes
make test-all
```

### Environment Variables

- `HG_HOST`: Hologram daemon socket path (default: `unix:///var/run/hologramd.sock`)
- `HOLOGRAM_VERBOSE`: Enable verbose mode with XHologram fields (set to `1`)
- `HOLOGRAM_ENFORCE`: Enable witness enforcement (set to `1`)
- `HOLOGRAM_NET`: Enable CTP96 network driver (set to `ctp96`)

### Individual Test Execution

```bash
# Run specific test categories
go test ./tests/go -run TestContainerHappyPath
go test ./tests/go -run TestEventsLifecycle
go test ./tests/go -run TestVolumesNamedAndBind

# Run with verbose output
go test ./tests/go -v

# Run benchmarks
go test ./tests/go -bench . -benchtime=20x
```

## CI Integration

The test suite is integrated with GitHub Actions through `.github/workflows/e2e-tests.yml`, providing:

- **Matrix Testing**: Multiple Go versions and test modes
- **Parallel Execution**: Different test categories run in parallel
- **Artifact Collection**: Logs and benchmark results on failure
- **Non-blocking Benchmarks**: Performance tests don't block PRs

## Test Philosophy

1. **Docker Compatibility First**: All tests validate that Hologram behaves like Docker
2. **Optional Extensions**: Hologram-specific features are additive, not breaking
3. **Comprehensive Coverage**: Tests cover the full Docker API surface
4. **Performance Awareness**: Benchmarks ensure no regressions
5. **Security Validation**: Enforce mode tests validate security policies

## Troubleshooting

### Common Issues

1. **Socket Connection Errors**: Ensure hologramd is running and accessible
2. **Image Pull Failures**: Check network connectivity and image availability
3. **Permission Errors**: Ensure proper socket permissions
4. **Test Timeouts**: Increase timeout values for slow environments

### Debug Mode

```bash
# Run with debug logging
HOLOGRAM_DEBUG=1 go test ./tests/go -v

# Run single test with verbose output
go test ./tests/go -run TestContainerHappyPath -v
```

## Contributing

When adding new tests:

1. Follow the existing naming conventions
2. Include proper cleanup in test functions
3. Add environment variable checks for optional features
4. Update this README with new test categories
5. Ensure tests work in all modes (compat, verbose, enforce)

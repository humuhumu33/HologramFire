# Hologram SDK Testing Guide

This document describes the comprehensive testing infrastructure for the Hologram SDK, designed to ensure Docker parity while adding Hologram magic.

## 🎯 Test Modes

The SDK supports three distinct test modes:

### 1. Compat Mode (Default)
- **Purpose**: Ensures Docker compatibility without Hologram features
- **Behavior**: No XHologram fields, never fail-closed
- **Use Case**: Drop-in Docker replacement

```bash
./run-tests.sh compat
```

### 2. Verbose Mode
- **Purpose**: Shows XHologram fields while preserving Docker UX
- **Behavior**: Adds XHologram progress messages and response fields
- **Use Case**: Development and debugging

```bash
./run-tests.sh verbose
```

### 3. Enforce Mode
- **Purpose**: Fail-closed on bad/missing witnesses
- **Behavior**: Returns Docker-style errors for invalid witnesses
- **Use Case**: Production security enforcement

```bash
./run-tests.sh enforce
```

## 🧪 Test Infrastructure

### Deterministic Test Knobs

For reliable testing without network dependencies:

```go
// Test images that always pass witness verification
"holo-test-ok:latest" -> "uor:test/ok:holo-test-ok:latest" -> ✅

// Test images that always fail witness verification  
"holo-test-bad:latest" -> "uor:test/bad:holo-test-bad:latest" -> ❌
```

### Per-Request Controls

Override global settings per request:

```bash
# Verbose mode via header
curl -H "X-Hologram-Verbose: 1" unix:///var/run/hologramd.sock/images/json

# Enforce mode via header
curl -H "X-Hologram-Enforce: 1" unix:///var/run/hologramd.sock/images/create?fromImage=holo-test-bad&tag=latest
```

## 🚀 Quick Start

### Local Development

```bash
# Start daemon in development mode
./scripts/dev.sh

# Or with specific environment
HOLOGRAM_VERBOSE=1 ./scripts/dev.sh
```

### Running Tests

```bash
# Run all test modes
cd tests && ./run_all.sh

# Run specific mode
./run-tests.sh verbose

# Run with custom environment
HOLOGRAM_VERBOSE=1 HOLOGRAM_ENFORCE=1 ./run-tests.sh compat
```

## 📊 Test Coverage

### Core Endpoints
- `/_ping` - Health check
- `/version` - Version information
- `/images/json` - Image listing
- `/images/create` - Image pulling
- `/containers/json` - Container listing
- `/networks` - Network listing

### Hologram Features
- UOR-ID resolution
- Witness verification
- XHologram progress messages
- Enforce mode error handling

### Golden Snapshots
- Docker-compatible response shapes
- Structure validation
- Automatic golden file generation

## 🔧 Test Files

```
tests/go/
├── enforce_test.go           # Enforce mode tests
├── verbose_inspect_test.go   # Verbose mode inspection
├── verbose_progress_test.go  # XHologram progress tests
├── parity_golden_test.go     # Docker parity validation
├── containers_lifecycle_test.go
├── network_test.go
├── volumes_test.go
└── golden/                   # Golden snapshots
    ├── version.json
    └── images.json
```

## 🐛 Debugging

### Logs
- Daemon logs: `/tmp/hologramd.log`
- Test artifacts: `/tmp/hologram-artifacts/`

### Common Issues

1. **Socket permissions**: Ensure `/var/run/hologramd.sock` has proper permissions
2. **Port conflicts**: Check if port 2375 is available (Windows)
3. **Test failures**: Check artifacts directory for detailed logs

### Verbose Output

```bash
# Enable verbose logging
HOLOGRAM_VERBOSE=1 ./scripts/dev.sh

# Check for XHologram fields
curl -H "X-Hologram-Verbose: 1" unix:///var/run/hologramd.sock/images/json | jq '.[0].XHologram'
```

## 🏗️ CI/CD Integration

### GitHub Actions
- Automatic test runs on PRs
- Artifact collection
- PR comment with results

### Local CI
```bash
# Run full test suite
cd tests && ./run_all.sh

# Check results
cat /tmp/hologram-artifacts/test-summary.json
```

## 📈 Performance Testing

```bash
# Benchmark container startup
go test -bench=BenchmarkStart ./tests/go/

# Latency testing
go test -run=TestLatency ./tests/go/
```

## 🔒 Security Testing

```bash
# Test enforce mode
./run-tests.sh enforce

# Verify witness rejection
curl -H "X-Hologram-Enforce: 1" \
  unix:///var/run/hologramd.sock/images/create?fromImage=holo-test-bad&tag=latest
```

## 📝 Writing Tests

### Basic Test Structure
```go
func TestMyFeature(t *testing.T) {
    if os.Getenv("HOLOGRAM_VERBOSE") != "1" {
        t.Skip("run with HOLOGRAM_VERBOSE=1")
    }
    
    ctx := context.Background()
    cli := hgClient(t)
    
    // Your test logic here
}
```

### Test Knobs Usage
```go
// Use deterministic test images
_, err := cli.ImagePull(ctx, "holo-test-ok:latest", types.ImagePullOptions{})
// This will always pass witness verification

_, err := cli.ImagePull(ctx, "holo-test-bad:latest", types.ImagePullOptions{})
// This will always fail witness verification
```

## 🎉 Success Criteria

A successful test run should show:
- ✅ All three modes pass
- ✅ Docker parity maintained
- ✅ XHologram features work in verbose mode
- ✅ Enforce mode blocks bad witnesses
- ✅ Golden snapshots match expected structure

## 📚 Additional Resources

- [Docker API Reference](https://docs.docker.com/engine/api/)
- [Hologram SDK Quickstart](../QUICKSTART.md)
- [Implementation Summary](../IMPLEMENTATION_SUMMARY.md)

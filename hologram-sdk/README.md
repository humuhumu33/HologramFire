# Hologram SDK

A drop-in compatible Docker SDK with native Hologram features.

## Architecture

This monorepo provides two layers:

1. **Compat Surface**: Drop-in replacement for Docker SDKs with identical UX, classes, methods, models, and error types
2. **Native Surface**: First-class support for UOR-IDs, witnesses, VPI leases, CTP-96, and the 12,288 space

## Components

- `engine/`: Hologram daemon (hologramd) with Docker Engine API compatibility
- `sdks/`: Language-specific SDKs (Python, Go, Node.js) in both compat and native variants
- `tools/`: Buildx driver and CLI utilities
- `tests/`: Parity tests, workload suites, and performance benchmarks
- `docs/`: Quickstart guides and deep-dive documentation

## Quick Start

### Docker-Compatible Mode

```bash
# Start hologramd (drop-in replacement for dockerd)
export DOCKER_HOST=unix:///var/run/hologramd.sock

# All Docker commands work unchanged
docker version
docker images
docker pull nginx:alpine
docker run --rm nginx:alpine echo "hello"
```

### Hologram Features (Optional)

```bash
# Enable verbose mode to see Hologram fields
export HOLOGRAM_VERBOSE=1
docker images  # Shows XHologram fields

# Enable enforce mode for fail-closed policies
export HOLOGRAM_ENFORCE=1
docker pull nginx:alpine  # Fails if witness invalid

# Set conformance profile
export HOLOGRAM_PROFILE=P-Network  # P-Core, P-Network, P-Runtime, P-Full
```

### SDK Usage

```bash
# Python (compat)
pip install hologram-docker
import hologram_docker as docker

# Python (native)
pip install hologram
import hologram

# Go (compat)
go get github.com/hologram/sdks/go/compat

# Go (native)
go get github.com/hologram/sdks/go/sdk

# Node.js (compat)
npm install hologramode

# Node.js (native)
npm install @hologram/sdk
```

## Integration Verification

See [INTEGRATION_VERIFICATION.md](INTEGRATION_VERIFICATION.md) for complete details on:

- Docker API compatibility matrix
- Blueprint integration verification
- Environment variable configuration
- CI/CD integration tests
- SDK compatibility tests

## Phase 2 - Docker Compatibility & Lifecycle

**NEW**: Phase 2 extends Docker compatibility to "day-1 usability" with full container lifecycle management, event streaming, volumes, networking, and Buildx driver hooks.

### Quick Start

```bash
# Build and start hologramd
make build
./engine/cmd/hologramd/hologramd

# Test Docker compatibility
export DOCKER_HOST=unix:///var/run/hologramd.sock
docker run -d --name test alpine sleep 3600
docker logs test
docker inspect test
```

### Features

- **Container Lifecycle**: Create, start, stop, logs, inspect, delete
- **Event Streaming**: Docker-compatible event bus with filtering
- **Volumes**: Named volumes and basic bind mount handling
- **Networking**: Bridge compatibility MVP and CTP-96 placeholder
- **Buildx Driver**: UOR-ID generation and witness verification
- **Verbose/Enforce Guards**: Conditional feature exposure and policy enforcement

### Documentation

- [Phase 2 README](PHASE2_README.md) - Complete documentation
- [Phase 2 Quick Start](PHASE2_QUICKSTART.md) - Getting started guide
- [Test Suite](tests/go/) - Comprehensive test coverage

### Testing

```bash
# Run all tests
make test

# Run specific test types
make compat      # Compatibility tests
make verbose     # Verbose mode tests
make enforce     # Enforce mode tests
make bench       # Benchmark tests
make e2e         # End-to-end tests
```

## Development

See individual component READMEs for development setup and contribution guidelines.

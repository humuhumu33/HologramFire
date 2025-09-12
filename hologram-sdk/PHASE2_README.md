# Hologram SDK Phase 2 - Docker Compatibility & Lifecycle

This document describes the Phase 2 implementation of the Hologram SDK, which extends Docker compatibility to "day-1 usability" with full container lifecycle management, event streaming, volumes, networking, and Buildx driver hooks.

## Overview

Phase 2 maintains 1:1 Docker UX parity while adding Hologram-specific features that are opt-in and namespaced under `XHologram`. The implementation includes:

- **Container Lifecycle**: Create, start, stop, logs, inspect, delete operations
- **Event Streaming**: Docker-compatible event bus with filtering
- **Volumes**: Named volumes and basic bind mount handling
- **Networking**: Bridge compatibility MVP and CTP-96 placeholder
- **Buildx Driver**: UOR-ID generation and witness verification
- **Verbose/Enforce Guards**: Conditional feature exposure and policy enforcement

## Architecture

### Core Components

```
hologram-sdk/engine/
├── cmd/hologramd/           # Main daemon entry point
├── internal/
│   ├── api/                 # HTTP API handlers
│   │   ├── server/          # Centralized handlers
│   │   │   ├── handlers.go  # Base handlers struct
│   │   │   ├── guards.go    # Verbose/enforce guards
│   │   │   ├── handlers_*.go # Specific endpoint handlers
│   │   └── server.go        # HTTP server setup
│   ├── runtime/             # Core runtime components
│   │   ├── state.go         # Container state store
│   │   ├── sandbox_proc.go  # Process runner MVP
│   │   ├── logs.go          # Log management
│   │   ├── lease.go         # VPI lease adapter
│   │   └── *.go            # Manager components
│   ├── events/              # Event system
│   │   ├── types.go         # Event message types
│   │   └── bus.go           # Pub/sub event bus
│   ├── volumes/             # Volume management
│   │   └── store.go         # Volume state store
│   └── networks/            # Network management
│       ├── store.go         # Network state store
│       ├── bridge.go        # Bridge network MVP
│       └── ctp96.go         # CTP-96 placeholder
└── tools/
    └── buildx-driver-hologram/ # Buildx driver
        └── main.go
```

### API Endpoints

#### Containers
- `POST /v1.41/containers/create` - Create container
- `POST /v1.41/containers/{id}/start` - Start container
- `POST /v1.41/containers/{id}/stop` - Stop container
- `GET /v1.41/containers/{id}/logs` - Get container logs
- `GET /v1.41/containers/{id}/json` - Inspect container
- `DELETE /v1.41/containers/{id}` - Delete container
- `GET /v1.41/containers/json` - List containers

#### Events
- `GET /v1.41/events` - Stream events

#### Volumes
- `GET /v1.41/volumes` - List volumes
- `POST /v1.41/volumes/create` - Create volume
- `GET /v1.41/volumes/{name}` - Inspect volume
- `DELETE /v1.41/volumes/{name}` - Delete volume
- `POST /v1.41/volumes/prune` - Prune volumes

#### Networks
- `GET /v1.41/networks` - List networks
- `POST /v1.41/networks/create` - Create network
- `GET /v1.41/networks/{id}` - Inspect network
- `POST /v1.41/networks/{id}/connect` - Connect container
- `POST /v1.41/networks/{id}/disconnect` - Disconnect container
- `DELETE /v1.41/networks/{id}` - Delete network

## Usage

### Basic Usage

Start the Hologram daemon:

```bash
# Default mode (permissive, no verbose output)
./hologramd

# Verbose mode (shows XHologram fields)
HOLOGRAM_VERBOSE=1 ./hologramd

# Enforce mode (strict policy enforcement)
HOLOGRAM_ENFORCE=1 ./hologramd

# Both verbose and enforce
HOLOGRAM_VERBOSE=1 HOLOGRAM_ENFORCE=1 ./hologramd
```

### Docker Client Compatibility

The daemon is compatible with standard Docker clients:

```bash
# Set DOCKER_HOST to use hologramd
export DOCKER_HOST=unix:///var/run/hologramd.sock

# Use standard Docker commands
docker run -d --name test alpine sleep 3600
docker logs test
docker inspect test
docker stop test
docker rm test
```

### Verbose Mode

When `HOLOGRAM_VERBOSE=1` or `X-Hologram-Verbose: 1` header is set, responses include additional Hologram-specific fields:

```json
{
  "Id": "container123",
  "Name": "/test",
  "State": "running",
  "XHologram": {
    "uor_id": "uor:abc123...",
    "witness_ok": true,
    "vpi_lease": "vpi-lease-abc123-456789",
    "meta_awareness": {
      "self_aware": true,
      "oracle_integrated": true
    }
  }
}
```

### Enforce Mode

When `HOLOGRAM_ENFORCE=1`, the system enforces strict policies:

- All containers must have valid UOR-IDs
- Witness verification is required
- VPI leases must be active
- Oracle integration is mandatory

### Buildx Driver

The Buildx driver generates UOR-IDs and witness metadata during builds:

```bash
# Build with Hologram driver
docker buildx build --driver hologram -t myimage .

# Verbose output shows UOR-ID and witness status
HOLOGRAM_VERBOSE=1 docker buildx build --driver hologram -t myimage .
```

## Testing

### Test Suite

The implementation includes comprehensive tests:

```bash
# Run all tests
make test

# Run specific test types
make compat      # Compatibility tests
make verbose     # Verbose mode tests
make enforce     # Enforce mode tests
make bench       # Benchmark tests
make e2e         # End-to-end tests
make race        # Race condition tests
```

### Test Files

- `tests/go/containers_lifecycle_test.go` - Container lifecycle tests
- `tests/go/events_test.go` - Event streaming tests
- `tests/go/volumes_test.go` - Volume CRUD tests
- `tests/go/network_test.go` - Network CRUD tests
- `tests/go/enforce_test.go` - Enforce mode tests
- `tests/go/verbose_inspect_test.go` - Verbose mode tests
- `tests/go/parity_golden_test.go` - Docker parity tests
- `tests/go/bench_start_latency_test.go` - Performance benchmarks

## Configuration

### Environment Variables

- `HOLOGRAM_VERBOSE=1` - Enable verbose mode
- `HOLOGRAM_ENFORCE=1` - Enable enforce mode
- `HOLOGRAM_TEST=1` - Test mode (used by test suite)

### Headers

- `X-Hologram-Verbose: 1` - Enable verbose mode for specific request

## Performance

### Benchmarks

The implementation includes performance benchmarks:

- Container start latency: < 100ms target
- Event streaming throughput: > 1000 events/sec
- Volume operations: < 50ms per operation
- Network operations: < 100ms per operation

### Monitoring

Built-in monitoring includes:

- Container lifecycle metrics
- Event bus performance
- Volume usage statistics
- Network connection tracking
- VPI lease status

## Security

### Fail-Closed Mechanism

When `HOLOGRAM_ENFORCE=1`:

- All operations require valid UOR-IDs
- Witness verification is mandatory
- VPI leases must be active
- Oracle integration is enforced

### Permissive Mode

Default mode allows operations with warnings:

- Missing UOR-IDs generate warnings
- Failed witness verification logs errors
- Inactive VPI leases are noted
- Oracle integration is optional

## Development

### Building

```bash
# Build hologramd
make build

# Build buildx driver
make build-driver

# Build everything
make build build-driver
```

### Running Tests

```bash
# Run all tests
make test

# Run specific test types
make compat verbose enforce bench e2e race
```

### Code Quality

```bash
# Format code
make fmt

# Lint code
make lint

# Run all checks
make check
```

## CI/CD

### GitHub Actions

The implementation includes a comprehensive CI/CD pipeline:

- **Test Suite**: Multiple test types (compat, verbose, enforce, race, e2e)
- **Benchmarks**: Performance testing
- **Docker Compatibility**: Docker client integration tests
- **Build**: Multi-platform builds
- **Security**: Security scanning
- **Lint**: Code quality checks
- **Integration**: End-to-end testing
- **Release**: Automated releases

### Workflow

The CI/CD pipeline runs on:

- Push to `main` or `develop` branches
- Pull requests to `main` or `develop` branches

All tests must pass before merging.

## Future Enhancements

### Phase 3 Roadmap

- **OS-level Isolation**: Real container sandboxing
- **Advanced Networking**: Full CTP-96 implementation
- **Storage Drivers**: Multiple volume backends
- **Orchestration**: Kubernetes integration
- **Monitoring**: Advanced metrics and alerting
- **Security**: Enhanced policy enforcement

### Contributing

1. Fork the repository
2. Create a feature branch
3. Implement changes with tests
4. Run the test suite
5. Submit a pull request

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## Support

For questions and support:

- Create an issue on GitHub
- Check the documentation
- Review the test suite for examples
- Join the community discussions

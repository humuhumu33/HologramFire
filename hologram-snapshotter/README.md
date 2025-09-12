# Hologram Snapshotter

A containerd snapshotter plugin that provides FUSE-based OCI layer serving with Hologram stack integration, including UOR-ID resolution, witness verification, and CTP-96 transport.

## Features

- **Drop-in Compatibility**: Works with Docker, nerdctl, and Kubernetes
- **FUSE Backend**: Read-only FUSE filesystem for serving OCI layers
- **Hologram Integration**: UOR-ID resolution, witness verification, CTP-96 transport
- **Enforce Mode**: Fail-closed operation when witness verification fails
- **Verbose Mode**: Enhanced metadata and logging
- **Telemetry**: Prometheus metrics and performance monitoring
- **Lazy Loading**: On-demand file reads for optimal performance

## Quick Start

### Prerequisites

- Go 1.21 or later
- containerd
- FUSE support (fuse3 package)
- nerdctl (for testing)

### Building

```bash
# Clone the repository
git clone https://github.com/hologram/hologram-snapshotter.git
cd hologram-snapshotter

# Build the binary
make build

# Or build for all platforms
make build-all
```

### Installation

```bash
# Install to system
make install

# Or manually copy the binary
sudo cp build/hologram-snapshotter /usr/local/bin/
```

### Configuration

Add the hologram snapshotter to your containerd configuration:

```toml
# /etc/containerd/config.toml
[plugins."io.containerd.snapshotter.v1.hologram"]
  root_path = "/var/lib/containerd/hologram"
```

### Usage

#### With nerdctl

```bash
# Pull an image using hologram snapshotter
nerdctl --snapshotter=hologram pull alpine:3.19

# Run a container
nerdctl --snapshotter=hologram run --rm alpine:3.19 echo "Hello Hologram"
```

#### With Docker

Docker will automatically use the hologram snapshotter if it's configured in containerd.

```bash
# Pull and run as usual
docker pull alpine:3.19
docker run --rm alpine:3.19 echo "Hello Hologram"
```

## Environment Variables

### HOLOGRAM_ENFORCE

Enable enforce mode (fail-closed on invalid witness):

```bash
export HOLOGRAM_ENFORCE=1
```

### HOLOGRAM_VERBOSE

Enable verbose mode (enhanced metadata and logging):

```bash
export HOLOGRAM_VERBOSE=1
```

### HOLOGRAM_NET

Set the network transport mode:

```bash
export HOLOGRAM_NET=ctp96
```

### HOLOGRAM_CTP96_ENDPOINT

Set the CTP-96 endpoint:

```bash
export HOLOGRAM_CTP96_ENDPOINT=http://localhost:8080
```

### HOLOGRAM_WITNESS_ENDPOINT

Set the witness verification endpoint:

```bash
export HOLOGRAM_WITNESS_ENDPOINT=http://localhost:8081
```

## Architecture

### Components

1. **Snapshotter**: Main containerd plugin interface
2. **FUSE Filesystem**: Read-only filesystem for serving OCI layers
3. **Resolver**: UOR-ID resolution and witness verification
4. **CTP-96 Client**: Transport protocol implementation
5. **Content Store**: Wrapper for containerd content operations
6. **Telemetry**: Metrics and performance monitoring

### Data Flow

```
Docker/nerdctl → containerd → Hologram Snapshotter → FUSE FS → OCI Layers
                                    ↓
                              UOR-ID Resolver → Witness Verification
                                    ↓
                              CTP-96 Transport → Content Store
```

## Development

### Setup

```bash
# Setup development environment
make dev-setup

# Run tests
make test

# Run integration tests
make test-integration

# Run with coverage
make test-coverage
```

### Code Quality

```bash
# Format code
make fmt

# Run linter
make lint

# Run security scan
make security

# Run go vet
make vet
```

### Docker Development

```bash
# Build Docker image
make docker-build

# Run Docker container
make docker-run
```

## Testing

### Unit Tests

```bash
make test
```

### Integration Tests

```bash
make test-integration
```

### Performance Tests

```bash
# Run performance benchmarks
go test -bench=. ./tests/performance/
```

## Monitoring

### Metrics

The hologram snapshotter exposes Prometheus metrics on port 8080:

- `hologram_snapshotter_operations_total`: Total snapshotter operations
- `hologram_fuse_operations_total`: Total FUSE operations
- `hologram_resolver_operations_total`: Total resolver operations
- `hologram_witness_operations_total`: Total witness operations
- `hologram_ctp96_operations_total`: Total CTP-96 operations
- `hologram_content_operations_total`: Total content operations
- `hologram_energy_hints`: Energy hints from CTP-96 sessions
- `hologram_lease_duration_seconds`: CTP-96 lease duration

### Logging

Enable verbose logging for detailed operation information:

```bash
export HOLOGRAM_VERBOSE=1
```

## Troubleshooting

### Common Issues

1. **FUSE not available**: Install fuse3 package
2. **Permission denied**: Ensure proper permissions for FUSE operations
3. **Snapshotter not registered**: Check containerd configuration
4. **Witness verification fails**: Check witness endpoint connectivity

### Debug Mode

Enable debug logging:

```bash
export HOLOGRAM_VERBOSE=1
export CONTAINERD_LOG_LEVEL=debug
```

### Logs

Check containerd logs for snapshotter operations:

```bash
journalctl -u containerd -f
```

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Run the test suite
6. Submit a pull request

## License

This project is licensed under the Apache License 2.0 - see the [LICENSE](LICENSE) file for details.

## Support

- Documentation: [docs/](docs/)
- Issues: [GitHub Issues](https://github.com/hologram/hologram-snapshotter/issues)
- Discussions: [GitHub Discussions](https://github.com/hologram/hologram-snapshotter/discussions)

## Roadmap

- [ ] Enhanced OCI layer support
- [ ] Advanced prefetching strategies
- [ ] Multi-registry support
- [ ] Kubernetes operator
- [ ] Web UI for monitoring
- [ ] Performance optimizations

# Hologram SDK Phase 2 - Quick Start Guide

This guide will get you up and running with Hologram SDK Phase 2 in minutes.

## Prerequisites

- Go 1.21 or later
- Docker (for compatibility testing)
- Make (for build automation)

## Installation

1. **Clone the repository**:
   ```bash
   git clone <repository-url>
   cd hologram-sdk
   ```

2. **Install dependencies**:
   ```bash
   make deps
   ```

3. **Build the daemon**:
   ```bash
   make build
   ```

## Quick Start

### 1. Start the Daemon

```bash
# Basic mode
./engine/cmd/hologramd/hologramd

# Verbose mode (shows XHologram fields)
HOLOGRAM_VERBOSE=1 ./engine/cmd/hologramd/hologramd

# Enforce mode (strict policies)
HOLOGRAM_ENFORCE=1 ./engine/cmd/hologramd/hologramd
```

### 2. Test Docker Compatibility

```bash
# Set DOCKER_HOST to use hologramd
export DOCKER_HOST=unix:///var/run/hologramd.sock

# Test basic operations
docker version
docker images
docker run -d --name test alpine sleep 3600
docker logs test
docker inspect test
docker stop test
docker rm test
```

### 3. Test Hologram Features

```bash
# Create a container with verbose output
HOLOGRAM_VERBOSE=1 docker run -d --name hologram-test alpine sleep 3600

# Inspect with verbose mode
HOLOGRAM_VERBOSE=1 docker inspect hologram-test

# Check for XHologram fields in the response
```

### 4. Test Volumes

```bash
# Create a volume
docker volume create test-vol

# List volumes
docker volume ls

# Inspect volume
docker volume inspect test-vol

# Use volume in container
docker run -d --name vol-test -v test-vol:/data alpine sleep 3600
```

### 5. Test Networks

```bash
# List networks
docker network ls

# Create a network
docker network create test-net

# Connect container to network
docker network connect test-net vol-test

# Inspect network
docker network inspect test-net
```

### 6. Test Events

```bash
# Stream events in another terminal
docker events

# In the main terminal, perform operations
docker run -d --name event-test alpine sleep 3600
docker stop event-test
docker rm event-test
```

## Testing

### Run the Test Suite

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

### Run Individual Tests

```bash
# Run specific test files
go test ./tests/go -run TestContainerLifecycle
go test ./tests/go -run TestEventsStream
go test ./tests/go -run TestVolumeCreate
go test ./tests/go -run TestNetworkCreate
```

## Buildx Driver

### Build the Driver

```bash
make build-driver
```

### Test the Driver

```bash
# Test basic build
./tools/buildx-driver-hologram/buildx-driver-hologram

# Test with verbose output
HOLOGRAM_VERBOSE=1 ./tools/buildx-driver-hologram/buildx-driver-hologram
```

## Configuration

### Environment Variables

- `HOLOGRAM_VERBOSE=1` - Enable verbose mode
- `HOLOGRAM_ENFORCE=1` - Enable enforce mode
- `HOLOGRAM_TEST=1` - Test mode (used by test suite)

### Headers

- `X-Hologram-Verbose: 1` - Enable verbose mode for specific request

## Troubleshooting

### Common Issues

1. **Permission denied on socket**:
   ```bash
   sudo chmod 666 /var/run/hologramd.sock
   ```

2. **Port already in use**:
   ```bash
   # Check what's using the port
   lsof -i :2375
   
   # Kill the process
   kill -9 <PID>
   ```

3. **Test failures**:
   ```bash
   # Run with verbose output
   go test ./tests/go -v
   
   # Check logs
   tail -f /var/log/hologramd.log
   ```

### Debug Mode

```bash
# Run with debug logging
HOLOGRAM_VERBOSE=1 ./engine/cmd/hologramd/hologramd
```

## Next Steps

1. **Read the full documentation**: See `PHASE2_README.md`
2. **Explore the test suite**: Check `tests/go/` for examples
3. **Review the API**: See `internal/api/` for endpoint implementations
4. **Check the runtime**: See `internal/runtime/` for core components

## Examples

### Container Lifecycle

```bash
# Create container
docker create --name test alpine sleep 3600

# Start container
docker start test

# Check status
docker ps

# Get logs
docker logs test

# Stop container
docker stop test

# Remove container
docker rm test
```

### Volume Management

```bash
# Create volume
docker volume create my-vol

# Use volume
docker run -d --name vol-test -v my-vol:/data alpine sleep 3600

# Inspect volume
docker volume inspect my-vol

# Remove volume
docker volume rm my-vol
```

### Network Management

```bash
# Create network
docker network create my-net

# Connect container
docker network connect my-net vol-test

# Inspect network
docker network inspect my-net

# Disconnect container
docker network disconnect my-net vol-test

# Remove network
docker network rm my-net
```

## Performance

### Benchmarks

```bash
# Run performance tests
make bench

# Check container start latency
go test ./tests/go -bench=BenchmarkContainerStart -v
```

### Monitoring

```bash
# Monitor daemon performance
HOLOGRAM_VERBOSE=1 ./engine/cmd/hologramd/hologramd

# Check system resources
top -p $(pgrep hologramd)
```

## Support

- **Documentation**: See `PHASE2_README.md`
- **Issues**: Create a GitHub issue
- **Tests**: Check `tests/go/` for examples
- **Community**: Join discussions

## License

MIT License - see LICENSE file for details.

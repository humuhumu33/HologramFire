# Hologram SDK Quick Start Guide

This guide shows you how to get started with the Hologram SDK, which provides Docker Engine API compatibility with native Hologram features.

## Prerequisites

- Go 1.21+ (for building the daemon)
- Python 3.8+ (for the Python client)
- Docker (for comparison testing)

## Building the Daemon

```bash
cd hologram-sdk/engine
go build -o hologramd ./cmd/hologramd
```

## Running the Daemon

### UNIX Socket Mode (Recommended)

```bash
# Start the daemon with UNIX socket
./hologramd --host=unix --socket=/var/run/hologramd.sock --socket-group=docker

# Test with curl
curl --unix-socket /var/run/hologramd.sock http://localhost/_ping
# Should return: OK

# Test with Docker CLI
export DOCKER_HOST=unix:///var/run/hologramd.sock
docker version
docker images
```

### TCP Mode (Development)

```bash
# Start the daemon with TCP (insecure without TLS)
./hologramd --host=0.0.0.0 --port=2376

# Test with curl
curl http://localhost:2376/_ping
# Should return: OK

# Test with Docker CLI
export DOCKER_HOST=tcp://localhost:2376
docker version
docker images
```

## Python Client Usage

### Basic Usage

```python
from hologram_docker import DockerClient

# Create client
client = DockerClient(base_url="unix:///var/run/hologramd.sock")

# Test connection
print("Ping:", client.ping())
print("Version:", client.version())

# List images
images = client.images.list()
print("Images:", len(images))

# Pull image with streaming
for event in client.images.pull("nginx", tag="alpine", stream=True):
    print("Pull event:", event.get('status', 'Unknown'))
```

### Environment Variables

```bash
# Set DOCKER_HOST to use Hologram daemon
export DOCKER_HOST=unix:///var/run/hologramd.sock

# Enable Hologram features
export HOLOGRAM_ENABLED=true
export HOLOGRAM_UOR_ID=true
export HOLOGRAM_WITNESS=true

# Use from_env() for automatic configuration
from hologram_docker import from_env
client = from_env()
```

## Testing

### Contract Checks

```bash
# Test basic endpoints
curl --unix-socket /var/run/hologramd.sock http://localhost/_ping
curl --unix-socket /var/run/hologramd.sock http://localhost/version
curl --unix-socket /var/run/hologramd.sock http://localhost/images/json
```

### Image Pull with Streaming

```bash
# Pull image with progress
curl --unix-socket /var/run/hologramd.sock \
  -X POST "http://localhost/images/create?fromImage=nginx&tag=alpine"
```

### Container Lifecycle

```bash
# Create container
curl --unix-socket /var/run/hologramd.sock \
  -X POST -H "Content-Type: application/json" \
  -d '{"Image": "hello-world:latest", "Cmd": ["/hello"]}' \
  http://localhost/containers/create

# Start container (replace CONTAINER_ID)
curl --unix-socket /var/run/hologramd.sock \
  -X POST http://localhost/containers/CONTAINER_ID/start

# Get container logs
curl --unix-socket /var/run/hologramd.sock \
  http://localhost/containers/CONTAINER_ID/logs

# Stop container
curl --unix-socket /var/run/hologramd.sock \
  -X POST http://localhost/containers/CONTAINER_ID/stop

# Delete container
curl --unix-socket /var/run/hologramd.sock \
  -X DELETE http://localhost/containers/CONTAINER_ID
```

### Comprehensive Testing

```bash
# Run the comprehensive test suite
python test_comprehensive.py

# Run parity tests
python tests/parity/test_parity.py
```

## Hologram Features

### Namespaced Extensions

Hologram-specific data is only included when verbose mode is enabled:

```bash
# Regular mode (Docker compatible)
curl --unix-socket /var/run/hologramd.sock http://localhost/images/json

# Verbose mode (includes XHologram data)
curl --unix-socket /var/run/hologramd.sock "http://localhost/images/json?verbose=true"
```

### Error Handling

All errors follow Docker's wire format:

```json
{
  "message": "No such image: nonexistent"
}
```

In verbose mode, additional context is provided:

```json
{
  "message": "No such image: nonexistent",
  "XHologram": {
    "reason": "Image not found in UOR registry",
    "uor_id": "uor:sha256:...",
    "witness": "verification_failed"
  }
}
```

## Systemd Service

For production deployment, use the provided systemd service:

```bash
# Copy service file
sudo cp deployment/hologramd.service /etc/systemd/system/

# Reload systemd
sudo systemctl daemon-reload

# Enable and start service
sudo systemctl enable hologramd
sudo systemctl start hologramd

# Check status
sudo systemctl status hologramd
```

## Security Notes

- **UNIX Socket**: Recommended for local access with proper permissions (0660)
- **TCP Mode**: Only use with TLS in production (`--tls --tls-cert --tls-key`)
- **Socket Group**: Use `--socket-group=docker` to allow docker group access

## Troubleshooting

### Common Issues

1. **Permission denied on socket**
   ```bash
   sudo chown root:docker /var/run/hologramd.sock
   sudo chmod 0660 /var/run/hologramd.sock
   ```

2. **Port already in use**
   ```bash
   # Use different port
   ./hologramd --host=0.0.0.0 --port=2377
   ```

3. **Python client import error**
   ```bash
   # Install dependencies
   pip install requests requests-unixsocket
   ```

### Logs

Check daemon logs for debugging:

```bash
# If running with systemd
sudo journalctl -u hologramd -f

# If running manually, logs go to stdout
./hologramd --log-level=debug
```

## Next Steps

- Explore Hologram-specific features (UOR-IDs, witnesses, VPI leases)
- Integrate with your existing Docker workflows
- Contribute to the project on GitHub

For more information, see the full documentation in the `docs/` directory.

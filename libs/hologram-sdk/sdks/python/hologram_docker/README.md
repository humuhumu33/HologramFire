# Hologram Docker SDK

A drop-in replacement for docker-py that provides Docker Engine API compatibility while adding optional Hologram features.

## Features

- **Docker API Compatibility**: Identical interface to docker-py
- **Hologram Extensions**: Optional UOR-IDs, witnesses, VPI leases, and CTP-96
- **UNIX Socket Support**: Connect to hologramd via UNIX socket
- **TCP Support**: Connect to hologramd via TCP
- **Streaming Support**: Real-time progress streaming for image operations

## Installation

```bash
pip install hologram-docker
```

## Quick Start

### Basic Usage (Docker Compatible)

```python
import hologram_docker as docker

# Create client (connects to hologramd by default)
client = docker.from_env()

# List images
images = client.images.list()
print(f"Found {len(images)} images")

# Pull an image
client.images.pull('nginx', 'alpine')

# Create and start a container
container = client.containers.create('nginx:alpine', command='echo "Hello World"')
container.start()
```

### Hologram Extensions

```python
import hologram_docker as docker

# Create client with Hologram features enabled
client = docker.from_env()

# List images with Hologram extensions
images = client.images.list(verbose=True)
for image in images:
    if hasattr(image, 'XHologram'):
        print(f"UOR-ID: {image.XHologram.get('uor_id')}")
        print(f"Witness OK: {image.XHologram.get('witness_ok')}")

# Pull image with Hologram features
client.images.pull('nginx', 'alpine', verbose=True)
```

## Configuration

### Environment Variables

- `DOCKER_HOST`: Docker daemon URL (default: `unix:///var/run/hologramd.sock`)
- `DOCKER_API_VERSION`: API version (default: `1.41`)
- `HOLOGRAM_VERBOSE`: Enable Hologram extensions (default: `false`)

### Connection Types

#### UNIX Socket (Default)
```python
client = docker.DockerClient(base_url='unix:///var/run/hologramd.sock')
```

#### TCP
```python
client = docker.DockerClient(base_url='tcp://localhost:2375')
```

#### HTTPS
```python
client = docker.DockerClient(base_url='https://localhost:2376', tls=True)
```

## API Reference

The API is identical to docker-py. See the [docker-py documentation](https://docker-py.readthedocs.io/) for detailed API reference.

### Hologram Extensions

When `verbose=True` is passed to methods, additional Hologram fields are included:

- `XHologram.uor_id`: Universal Object Reference ID
- `XHologram.witness_ok`: Witness verification status
- `XHologram.vpi_lease`: VPI lease information
- `XHologram.ctp96`: CTP-96 transport status
- `XHologram.space_12288`: 12,288 space allocation
- `XHologram.meta_aware`: Meta-awareness status
- `XHologram.oracle`: Oracle connection status

## Examples

### Image Operations

```python
import hologram_docker as docker

client = docker.from_env()

# List all images
images = client.images.list(all=True)

# Pull image with progress
for line in client.images.pull('nginx', 'alpine', stream=True):
    print(line)

# Inspect image with Hologram extensions
image = client.images.inspect('nginx:alpine', verbose=True)
if 'XHologram' in image:
    print(f"UOR-ID: {image['XHologram']['uor_id']}")
```

### Container Operations

```python
import hologram_docker as docker

client = docker.from_env()

# Create container
container = client.containers.create(
    'nginx:alpine',
    command='nginx -g "daemon off;"',
    ports={'80/tcp': 8080}
)

# Start container
container.start()

# Get container logs
logs = container.logs(stream=True, follow=True)
for line in logs:
    print(line.decode('utf-8'))
```

### Network Operations

```python
import hologram_docker as docker

client = docker.from_env()

# Create network
network = client.networks.create('my-network', driver='bridge')

# List networks with Hologram extensions
networks = client.networks.list(verbose=True)
for net in networks:
    if 'XHologram' in net:
        print(f"CTP-96: {net['XHologram'].get('ctp96')}")
```

## Error Handling

```python
import hologram_docker as docker
from hologram_docker.errors import ImageNotFound, ContainerNotFound

client = docker.from_env()

try:
    image = client.images.get('nonexistent:latest')
except ImageNotFound:
    print("Image not found")

try:
    container = client.containers.get('nonexistent')
except ContainerNotFound:
    print("Container not found")
```

## Development

### Setup

```bash
git clone https://github.com/hologram/sdks.git
cd sdks/sdks/python/hologram_docker
pip install -e .
```

### Testing

```bash
pytest
```

### Linting

```bash
black .
flake8 .
mypy .
```

## License

MIT License - see LICENSE file for details.

## Contributing

Contributions are welcome! Please see CONTRIBUTING.md for guidelines.
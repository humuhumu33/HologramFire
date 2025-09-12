# Hologram SDK Quickstart

**Docker-compatible container runtime with cryptographic provenance**

Get started with Hologram SDK in 60 seconds. It's Docker, but with superpowers.

## Install & Start

```bash
# Build and start hologramd
cd hologram-sdk/engine
go run cmd/hologramd/main.go --host=unix --socket=/var/run/hologramd.sock

# Set DOCKER_HOST (just like Docker)
export DOCKER_HOST=unix:///var/run/hologramd.sock
```

## It's Just Docker

```bash
# All your Docker commands work unchanged
docker version
docker images
docker run --rm hello-world:latest
docker pull nginx:alpine
docker run -d --name web -p 8080:80 nginx:alpine
```

**That's it.** No learning curve, no new commands, no breaking changes.

## Unlock the Magic

Want to see what makes Hologram special? It's one environment variable:

```bash
# Enable verbose mode to see Hologram fields
export HOLOGRAM_VERBOSE=1

# Now you see provenance information
docker images  # Shows XHologram fields
docker inspect nginx:alpine  # Shows UOR-IDs and witness status
```

## Production Security

For production environments, enable fail-closed mode:

```bash
# Enforce witness verification (blocks invalid images)
export HOLOGRAM_ENFORCE=1

# Now operations fail if witness verification fails
docker run --rm nginx:alpine  # Fails if witness is invalid
```

## Python SDK

```bash
# Install the Docker-compatible Python client
pip install hologram-docker

# Use it exactly like docker-py
import hologram_docker as docker
client = docker.from_env()
images = client.images.list()
```

## What You Get

- **Docker compatibility**: 100% API compatibility
- **Cryptographic provenance**: Every image gets a UOR-ID
- **Witness verification**: Cryptographic proof of integrity
- **Fail-closed security**: Block unverified images
- **Energy tracking**: Monitor resource usage
- **Zero learning curve**: Start with Docker knowledge

## Next Steps

- Run the [complete demo](examples/run-all-examples.sh) to see all features
- Read [AHA-DEMO.md](AHA-DEMO.md) for the full journey
- Check out [examples/](examples/) for detailed scenarios

**Welcome to the future of container runtimes.** 🚀

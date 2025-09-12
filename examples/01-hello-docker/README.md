# Example 1: Hello Docker

**Identical to Docker. No Hologram terms yet.**

This example demonstrates that Hologram SDK behaves exactly like Docker in compatibility mode. All Docker commands work unchanged.

## Prerequisites

1. Start hologramd daemon:
   ```bash
   cd hologram-sdk/engine
   go run cmd/hologramd/main.go --host=unix --socket=/var/run/hologramd.sock
   ```

2. Set DOCKER_HOST environment variable:
   ```bash
   export DOCKER_HOST=unix:///var/run/hologramd.sock
   ```

## Running the Example

```bash
# Test basic connectivity
docker version

# List images (will show seeded hello-world image)
docker images

# Run a simple container
docker run --rm hello-world:latest

# Pull and run nginx
docker pull nginx:alpine
docker run -d --name web -p 8080:80 nginx:alpine
docker logs -f web

# Clean up
docker stop web
docker rm web
```

## What You'll See

- All commands work exactly like Docker
- No Hologram-specific output or fields
- Standard Docker API responses
- Identical behavior to dockerd

## Key Points

- **Zero learning curve**: Existing Docker knowledge applies
- **Drop-in replacement**: No code changes needed
- **Full compatibility**: All Docker CLI commands work
- **No Hologram exposure**: Features are hidden by default

This is the foundation that makes the "aha moment" possible - users can start with familiar Docker commands and gradually discover Hologram's power.

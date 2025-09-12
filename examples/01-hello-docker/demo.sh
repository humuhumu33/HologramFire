#!/bin/bash

# Example 1: Hello Docker - Identical to Docker
# This script demonstrates that Hologram SDK behaves exactly like Docker

set -e

echo "🚀 Example 1: Hello Docker"
echo "=========================="
echo ""

# Check if hologramd is running
if ! curl -s --unix-socket /var/run/hologramd.sock http://localhost/_ping > /dev/null; then
    echo "❌ hologramd is not running. Please start it first:"
    echo "   cd hologram-sdk/engine && go run cmd/hologramd/main.go --host=unix --socket=/var/run/hologramd.sock"
    exit 1
fi

echo "✅ hologramd is running"
echo ""

# Set DOCKER_HOST
export DOCKER_HOST=unix:///var/run/hologramd.sock

echo "📋 Testing basic connectivity..."
docker version
echo ""

echo "📋 Listing images (shows seeded hello-world)..."
docker images
echo ""

echo "📋 Running hello-world container..."
docker run --rm hello-world:latest
echo ""

echo "📋 Pulling nginx:alpine..."
docker pull nginx:alpine
echo ""

echo "📋 Running nginx container..."
docker run -d --name web -p 8080:80 nginx:alpine
echo ""

echo "📋 Checking container logs..."
sleep 2
docker logs web
echo ""

echo "📋 Cleaning up..."
docker stop web
docker rm web
echo ""

echo "✅ Example 1 complete!"
echo ""
echo "Key takeaways:"
echo "- All Docker commands work unchanged"
echo "- No Hologram-specific output"
echo "- Identical behavior to dockerd"
echo "- Zero learning curve"

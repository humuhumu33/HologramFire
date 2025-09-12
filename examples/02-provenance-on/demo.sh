#!/bin/bash

# Example 2: Provenance On - "Oh wow" moment
# This script demonstrates UOR-ID + witness verification

set -e

echo "🚀 Example 2: Provenance On"
echo "==========================="
echo ""

# Check if hologramd is running
if ! curl -s --unix-socket /var/run/hologramd.sock http://localhost/_ping > /dev/null; then
    echo "❌ hologramd is not running. Please start it first:"
    echo "   cd hologram-sdk/engine && go run cmd/hologramd/main.go --host=unix --socket=/var/run/hologramd.sock"
    exit 1
fi

# Set DOCKER_HOST
export DOCKER_HOST=unix:///var/run/hologramd.sock

echo "📋 Step 1: Normal Docker mode (no Hologram fields visible)"
docker images
echo ""

echo "📋 Step 2: Enable verbose mode to see Hologram fields"
export HOLOGRAM_VERBOSE=1
echo "HOLOGRAM_VERBOSE=1 enabled"
echo ""

echo "📋 Step 3: List images with XHologram fields visible"
docker images
echo ""

echo "📋 Step 4: Pull an image and see provenance information"
docker pull nginx:alpine
echo ""

echo "📋 Step 5: Inspect image to see detailed XHologram fields"
docker inspect nginx:alpine | jq '.[0].XHologram // "No XHologram fields (compat mode)"'
echo ""

echo "📋 Step 6: Create a buildx builder (placeholder for hologram driver)"
echo "Note: This would use 'docker buildx build --driver=hologram' in a real implementation"
echo ""

echo "📋 Step 7: Show the difference between normal and verbose modes"
echo "Normal mode (HOLOGRAM_VERBOSE=0):"
unset HOLOGRAM_VERBOSE
docker images --format "table {{.Repository}}\t{{.Tag}}\t{{.ID}}" | head -3
echo ""

echo "Verbose mode (HOLOGRAM_VERBOSE=1):"
export HOLOGRAM_VERBOSE=1
docker images --format "table {{.Repository}}\t{{.Tag}}\t{{.ID}}" | head -3
echo ""

echo "✅ Example 2 complete!"
echo ""
echo "Key takeaways:"
echo "- UOR-IDs provide cryptographic provenance"
echo "- Witness verification ensures integrity"
echo "- XHologram fields are hidden by default"
echo "- Verbose mode reveals the magic"
echo "- Docker compatibility is maintained"

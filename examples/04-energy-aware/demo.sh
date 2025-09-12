#!/bin/bash

# Example 4: Energy-Aware Runtime - Advanced insights
# This script demonstrates VPI leases + energy/compute tracking

set -e

echo "🚀 Example 4: Energy-Aware Runtime"
echo "=================================="
echo ""

# Check if hologramd is running
if ! curl -s --unix-socket /var/run/hologramd.sock http://localhost/_ping > /dev/null; then
    echo "❌ hologramd is not running. Please start it first:"
    echo "   cd hologram-sdk/engine && go run cmd/hologramd/main.go --host=unix --socket=/var/run/hologramd.sock"
    exit 1
fi

# Set DOCKER_HOST and enable verbose mode
export DOCKER_HOST=unix:///var/run/hologramd.sock
export HOLOGRAM_VERBOSE=1

echo "📋 Step 1: Enable verbose mode for full Hologram insights"
echo "HOLOGRAM_VERBOSE=1 enabled"
echo ""

echo "📋 Step 2: Run a container and see VPI lease information"
docker run -d --name web -p 8080:80 nginx:alpine
echo "✅ Container started with VPI lease"
echo ""

echo "📋 Step 3: Check standard Docker stats"
docker stats --no-stream
echo ""

echo "📋 Step 4: Inspect container to see XHologram fields"
echo "VPI lease information:"
docker inspect web | jq '.[0].XHologram.lease_id // "No lease_id (compat mode)"'
echo ""

echo "Energy budget information:"
docker inspect web | jq '.[0].XHologram.budget_delta // "No budget_delta (compat mode)"'
echo ""

echo "📋 Step 5: Show full XHologram structure"
echo "Complete XHologram fields:"
docker inspect web | jq '.[0].XHologram // "No XHologram fields (compat mode)"'
echo ""

echo "📋 Step 6: Demonstrate energy and compute insights"
echo "This shows the full power of Hologram runtime:"
echo "  - VPI leases for virtual process isolation"
echo "  - Energy tracking and budget management"
echo "  - Detailed compute metrics and insights"
echo "  - Advanced observability beyond standard Docker"
echo ""

echo "📋 Step 7: Show the progression of Hologram features"
echo "Example 1: Docker compatibility (zero learning curve)"
echo "Example 2: Provenance tracking (UOR-IDs + witnesses)"
echo "Example 3: Fail-closed security (enforce mode)"
echo "Example 4: Energy-aware runtime (VPI + insights)"
echo ""

echo "📋 Step 8: Clean up"
docker stop web
docker rm web
echo "✅ Container cleaned up"
echo ""

echo "✅ Example 4 complete!"
echo ""
echo "Key takeaways:"
echo "- VPI leases provide virtual process isolation"
echo "- Energy tracking enables cost optimization"
echo "- Compute insights support performance tuning"
echo "- Advanced observability beyond standard Docker"
echo "- Complete container runtime with cryptographic guarantees"
echo ""
echo "🎉 You've now seen the full Hologram ecosystem:"
echo "   Docker compatibility + Provenance + Security + Energy awareness"

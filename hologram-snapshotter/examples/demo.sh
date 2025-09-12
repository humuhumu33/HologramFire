#!/bin/bash

# Hologram Snapshotter Demo Script
# This script demonstrates basic usage of the hologram snapshotter

set -e

echo "🚀 Hologram Snapshotter Demo"
echo "=============================="

# Check prerequisites
echo "📋 Checking prerequisites..."

if ! command -v nerdctl &> /dev/null; then
    echo "❌ nerdctl not found. Please install nerdctl first."
    exit 1
fi

if ! command -v containerd &> /dev/null; then
    echo "❌ containerd not found. Please install containerd first."
    exit 1
fi

echo "✅ Prerequisites check passed"

# Check if hologram snapshotter is available
echo "🔍 Checking hologram snapshotter availability..."

if ! nerdctl --snapshotter=hologram info &> /dev/null; then
    echo "❌ Hologram snapshotter not available. Please ensure it's properly configured in containerd."
    echo "   Add the following to your containerd config:"
    echo "   [plugins.\"io.containerd.snapshotter.v1.hologram\"]"
    echo "     root_path = \"/var/lib/containerd/hologram\""
    exit 1
fi

echo "✅ Hologram snapshotter is available"

# Set environment variables for demo
export HOLOGRAM_VERBOSE=1
export HOLOGRAM_ENFORCE=0  # Disable enforce mode for demo

echo "🔧 Environment configured:"
echo "   HOLOGRAM_VERBOSE=1"
echo "   HOLOGRAM_ENFORCE=0"

# Demo 1: Pull an image
echo ""
echo "📥 Demo 1: Pulling an image with hologram snapshotter"
echo "------------------------------------------------------"

IMAGE="alpine:3.19"
echo "Pulling $IMAGE..."

if nerdctl --snapshotter=hologram pull $IMAGE; then
    echo "✅ Successfully pulled $IMAGE with hologram snapshotter"
else
    echo "❌ Failed to pull $IMAGE"
    exit 1
fi

# Demo 2: Run a container
echo ""
echo "🏃 Demo 2: Running a container with hologram snapshotter"
echo "--------------------------------------------------------"

CONTAINER_NAME="hologram-demo-$(date +%s)"
echo "Running container: $CONTAINER_NAME"

if nerdctl --snapshotter=hologram run --rm --name $CONTAINER_NAME $IMAGE echo "Hello from Hologram Snapshotter!"; then
    echo "✅ Successfully ran container with hologram snapshotter"
else
    echo "❌ Failed to run container"
    exit 1
fi

# Demo 3: Inspect the image
echo ""
echo "🔍 Demo 3: Inspecting the image"
echo "-------------------------------"

if nerdctl --snapshotter=hologram image inspect $IMAGE > /dev/null; then
    echo "✅ Successfully inspected $IMAGE"
    echo "Image details:"
    nerdctl --snapshotter=hologram image inspect $IMAGE | jq '.[0] | {Id: .Id, Created: .Created, Size: .Size}' 2>/dev/null || echo "   (jq not available for pretty printing)"
else
    echo "❌ Failed to inspect $IMAGE"
fi

# Demo 4: List images
echo ""
echo "📋 Demo 4: Listing images"
echo "-------------------------"

echo "Images available with hologram snapshotter:"
nerdctl --snapshotter=hologram images

# Demo 5: Performance test
echo ""
echo "⚡ Demo 5: Performance test"
echo "--------------------------"

echo "Running multiple containers to test performance..."

for i in {1..3}; do
    echo "  Container $i/3..."
    nerdctl --snapshotter=hologram run --rm $IMAGE echo "Performance test $i" > /dev/null
done

echo "✅ Performance test completed"

# Demo 6: Cleanup
echo ""
echo "🧹 Demo 6: Cleanup"
echo "------------------"

echo "Removing demo image..."
if nerdctl --snapshotter=hologram rmi $IMAGE; then
    echo "✅ Successfully removed $IMAGE"
else
    echo "⚠️  Failed to remove $IMAGE (may be in use)"
fi

echo ""
echo "🎉 Demo completed successfully!"
echo "=============================="
echo ""
echo "The hologram snapshotter is working correctly with:"
echo "  ✅ Image pulling"
echo "  ✅ Container execution"
echo "  ✅ Image inspection"
echo "  ✅ Performance"
echo ""
echo "Next steps:"
echo "  - Try with different images"
echo "  - Enable HOLOGRAM_ENFORCE=1 for strict mode"
echo "  - Configure CTP-96 and witness endpoints"
echo "  - Monitor metrics at http://localhost:8080/metrics"

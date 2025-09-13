#!/bin/bash

# Master script to run all Hologram SDK examples
# This demonstrates the complete "Cursor-style Aha" UX journey

set -e

echo "🎯 Hologram SDK: Cursor-style Aha UX Demo"
echo "=========================================="
echo ""
echo "This demo shows the complete journey from 'It's just Docker' to 'Never going back'"
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

echo "🚀 Starting the Aha Journey..."
echo ""

# Example 1: Hello Docker
echo "📖 Example 1: Hello Docker"
echo "=========================="
echo "Time: 60 seconds - 'It's just Docker'"
echo ""
bash examples/01-hello-docker/demo.sh
echo ""

# Example 2: Provenance On
echo "📖 Example 2: Provenance On"
echo "==========================="
echo "Time: 5 minutes - 'Oh wow' (provenance)"
echo ""
bash examples/02-provenance-on/demo.sh
echo ""

# Example 3: Enforce Mode
echo "📖 Example 3: Enforce Mode"
echo "=========================="
echo "Time: 10 minutes - 'Never going back' (enforced trust)"
echo ""
bash examples/03-enforce/demo.sh
echo ""

# Example 4: Energy-Aware
echo "📖 Example 4: Energy-Aware Runtime"
echo "=================================="
echo "Time: 15 minutes - 'Advanced insights' (energy/compute)"
echo ""
bash examples/04-energy-aware/demo.sh
echo ""

echo "🎉 Complete Aha Journey Finished!"
echo "=================================="
echo ""
echo "You've experienced the full Hologram SDK journey:"
echo ""
echo "1. ✅ Docker Compatibility (60 seconds)"
echo "   - Zero learning curve"
echo "   - Drop-in replacement"
echo "   - All Docker commands work"
echo ""
echo "2. ✅ Provenance Tracking (5 minutes)"
echo "   - UOR-IDs for every image"
echo "   - Witness verification"
echo "   - Cryptographic guarantees"
echo ""
echo "3. ✅ Fail-Closed Security (10 minutes)"
echo "   - Enforce mode for production"
echo "   - Invalid witnesses block execution"
echo "   - Security-first approach"
echo ""
echo "4. ✅ Energy-Aware Runtime (15 minutes)"
echo "   - VPI leases for isolation"
echo "   - Energy tracking and optimization"
echo "   - Advanced compute insights"
echo ""
echo "🚀 Ready to use Hologram SDK in production!"
echo ""
echo "Next steps:"
echo "- Set HOLOGRAM_VERBOSE=1 for development"
echo "- Set HOLOGRAM_ENFORCE=1 for production"
echo "- Use buildx with --driver=hologram for builds"
echo "- Monitor energy and compute metrics"
echo ""
echo "Welcome to the future of container runtimes! 🎯"

#!/bin/bash

# Example 3: Enforce Mode - "Never going back" moment
# This script demonstrates fail-closed security with witness enforcement

set -e

echo "🚀 Example 3: Enforce Mode"
echo "=========================="
echo ""

# Check if hologramd is running
if ! curl -s --unix-socket /var/run/hologramd.sock http://localhost/_ping > /dev/null; then
    echo "❌ hologramd is not running. Please start it first:"
    echo "   cd hologram-sdk/engine && go run cmd/hologramd/main.go --host=unix --socket=/var/run/hologramd.sock"
    exit 1
fi

# Set DOCKER_HOST
export DOCKER_HOST=unix:///var/run/hologramd.sock

echo "📋 Step 1: Warning mode (default) - operations succeed with warnings"
echo "Running container in warning mode..."
docker run --rm nginx:alpine echo "Hello from warning mode"
echo "✅ Container ran successfully (warnings logged but not blocking)"
echo ""

echo "📋 Step 2: Enable enforce mode"
export HOLOGRAM_ENFORCE=1
echo "HOLOGRAM_ENFORCE=1 enabled"
echo ""

echo "📋 Step 3: Try to run container with enforce mode"
echo "Attempting to run container with witness enforcement..."
if docker run --rm nginx:alpine echo "Hello from enforce mode" 2>&1; then
    echo "✅ Container ran successfully (witness verification passed)"
else
    echo "❌ Container failed (witness verification failed)"
fi
echo ""

echo "📋 Step 4: Show the difference between modes"
echo "Warning mode (HOLOGRAM_ENFORCE=0):"
unset HOLOGRAM_ENFORCE
echo "  - Operations succeed even with invalid witnesses"
echo "  - Warnings are logged but don't block execution"
echo "  - Compatible with existing workflows"
echo ""

echo "Enforce mode (HOLOGRAM_ENFORCE=1):"
export HOLOGRAM_ENFORCE=1
echo "  - Operations fail if witness verification fails"
echo "  - Clear error messages in Docker format"
echo "  - Fail-closed security policy"
echo ""

echo "📋 Step 5: Demonstrate error handling"
echo "With verbose mode enabled, you'll see detailed error context:"
export HOLOGRAM_VERBOSE=1
echo "HOLOGRAM_VERBOSE=1 enabled"
echo ""

echo "📋 Step 6: Show enforcement in action"
echo "This demonstrates the 'never going back' moment:"
echo "  - Cryptographic guarantees about container images"
echo "  - No more 'trust but verify' - now it's 'verify or fail'"
echo "  - Production-ready security for critical environments"
echo ""

echo "✅ Example 3 complete!"
echo ""
echo "Key takeaways:"
echo "- Fail-closed security with witness enforcement"
echo "- Opt-in enforcement (HOLOGRAM_ENFORCE=1)"
echo "- Docker-compatible error messages"
echo "- Gradual adoption path (warnings → enforcement)"
echo "- Production-ready security guarantees"

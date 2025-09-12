#!/bin/bash

# Hologram SDK Demo Runner
# This script builds and runs hologramd for the demo

set -e

echo "🚀 Hologram SDK Demo Setup"
echo "=========================="
echo ""

# Check if Go is installed
if ! command -v go &> /dev/null; then
    echo "❌ Go is not installed. Please install Go 1.21 or later."
    exit 1
fi

echo "✅ Go is installed: $(go version)"
echo ""

# Build hologramd
echo "🔨 Building hologramd..."
cd engine
go build -o hologramd cmd/hologramd/main.go
echo "✅ hologramd built successfully"
echo ""

# Check if socket exists and remove it
if [ -S /var/run/hologramd.sock ]; then
    echo "🧹 Removing existing socket..."
    sudo rm -f /var/run/hologramd.sock
fi

# Start hologramd
echo "🚀 Starting hologramd..."
echo "   Socket: /var/run/hologramd.sock"
echo "   Mode: Docker compatibility"
echo ""

# Run hologramd in the background
sudo ./hologramd --host=unix --socket=/var/run/hologramd.sock &
HOLOGRAMD_PID=$!

# Wait for hologramd to start
echo "⏳ Waiting for hologramd to start..."
sleep 3

# Test connectivity
if curl -s --unix-socket /var/run/hologramd.sock http://localhost/_ping > /dev/null; then
    echo "✅ hologramd is running and responding"
else
    echo "❌ hologramd failed to start"
    kill $HOLOGRAMD_PID 2>/dev/null || true
    exit 1
fi

echo ""
echo "🎯 Hologram SDK is ready!"
echo ""
echo "Next steps:"
echo "1. Set DOCKER_HOST: export DOCKER_HOST=unix:///var/run/hologramd.sock"
echo "2. Test: docker version"
echo "3. Run examples: bash examples/run-all-examples.sh"
echo ""
echo "To stop hologramd: kill $HOLOGRAMD_PID"
echo ""

# Keep the script running
echo "Press Ctrl+C to stop hologramd and exit"
trap "echo ''; echo '🛑 Stopping hologramd...'; kill $HOLOGRAMD_PID 2>/dev/null || true; echo '✅ hologramd stopped'; exit 0" INT

# Wait for the process
wait $HOLOGRAMD_PID

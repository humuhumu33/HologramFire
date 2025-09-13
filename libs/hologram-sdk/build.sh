#!/bin/bash
set -e

echo "Building Hologram SDK..."

# Build the Go engine
echo "Building hologramd daemon..."
cd engine
go build -o ../bin/hologramd ./cmd/hologramd
echo "✓ hologramd built successfully"

# Build Python SDK
echo "Building Python SDK..."
cd ../sdks/python/hologram_docker
python -m pip install -e .
echo "✓ Python SDK built successfully"

echo "Build complete!"
echo ""
echo "To run the daemon:"
echo "  ./bin/hologramd --host=unix --socket=/var/run/hologramd.sock"
echo ""
echo "To test the daemon:"
echo "  python ../test_hologramd.py"

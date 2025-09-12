#!/bin/bash

# Run hologramd daemon for testing

echo "Starting Hologram daemon..."

# Build the daemon
cd engine
go build -o hologramd ./cmd/hologramd

if [ $? -ne 0 ]; then
    echo "Failed to build hologramd"
    exit 1
fi

echo "Built hologramd successfully"

# Run the daemon with UNIX socket
echo "Starting daemon on UNIX socket..."
sudo ./hologramd --host=unix --hologram-enabled --hologram-uor-id --hologram-witness

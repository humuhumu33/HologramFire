#!/usr/bin/env bash
set -euo pipefail

# Hologram SDK Development Helper
# Quick daemon startup with logging

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENGINE_DIR="$SCRIPT_DIR/../engine"
SOCKET_PATH="/var/run/hologramd.sock"
LOG_FILE="/tmp/hologramd.log"

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

log() {
    echo -e "${BLUE}[$(date +'%H:%M:%S')]${NC} $1"
}

success() {
    echo -e "${GREEN}✓${NC} $1"
}

cleanup() {
    log "Cleaning up..."
    rm -f "$SOCKET_PATH"
}

trap cleanup EXIT

log "Hologram SDK Development Mode"
log "============================="

# Build the daemon
log "Building hologramd..."
cd "$ENGINE_DIR"
if ! go build -o hologramd ./cmd/hologramd; then
    echo "Failed to build hologramd"
    exit 1
fi
success "Built hologramd successfully"

# Clean up any existing socket
rm -f "$SOCKET_PATH"

# Set environment variables from command line or defaults
export HOLOGRAM_VERBOSE=${HOLOGRAM_VERBOSE:-}
export HOLOGRAM_ENFORCE=${HOLOGRAM_ENFORCE:-}

log "Starting hologramd..."
log "Environment:"
log "  HOLOGRAM_VERBOSE=$HOLOGRAM_VERBOSE"
log "  HOLOGRAM_ENFORCE=$HOLOGRAM_ENFORCE"
log "  Socket: $SOCKET_PATH"
log "  Logs: $LOG_FILE"
log ""
log "Press Ctrl+C to stop"
log ""

# Start daemon with live output
./hologramd --host=unix --socket-path="$SOCKET_PATH" 2>&1 | tee "$LOG_FILE"

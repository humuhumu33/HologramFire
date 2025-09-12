#!/usr/bin/env bash
set -euo pipefail

# Hologram SDK Test Runner
# Supports 3 modes: compat, verbose, enforce

MODE=${1:-compat}
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENGINE_DIR="$SCRIPT_DIR/engine"
TESTS_DIR="$SCRIPT_DIR/../tests/go"
SOCKET_PATH="/var/run/hologramd.sock"
PID_FILE="$SCRIPT_DIR/.pid"
LOG_FILE="/tmp/hologramd.log"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

log() {
    echo -e "${BLUE}[$(date +'%H:%M:%S')]${NC} $1"
}

success() {
    echo -e "${GREEN}✓${NC} $1"
}

error() {
    echo -e "${RED}✗${NC} $1"
}

warn() {
    echo -e "${YELLOW}⚠${NC} $1"
}

cleanup() {
    log "Cleaning up..."
    if [ -f "$PID_FILE" ]; then
        local pid=$(cat "$PID_FILE")
        if kill -0 "$pid" 2>/dev/null; then
            log "Stopping hologramd (PID: $pid)"
            kill "$pid" || true
            sleep 2
            kill -0 "$pid" 2>/dev/null && kill -9 "$pid" || true
        fi
        rm -f "$PID_FILE"
    fi
    rm -f "$SOCKET_PATH"
}

trap cleanup EXIT

build_daemon() {
    log "Building hologramd..."
    cd "$ENGINE_DIR"
    if ! go build -o hologramd ./cmd/hologramd; then
        error "Failed to build hologramd"
        exit 1
    fi
    success "Built hologramd successfully"
}

start_daemon() {
    local verbose=${1:-}
    local enforce=${2:-}
    
    log "Starting hologramd in $MODE mode..."
    
    # Clean up any existing socket
    rm -f "$SOCKET_PATH"
    
    # Set environment variables
    export HOLOGRAM_VERBOSE="$verbose"
    export HOLOGRAM_ENFORCE="$enforce"
    
    # Start daemon in background
    cd "$ENGINE_DIR"
    ./hologramd --host=unix --socket-path="$SOCKET_PATH" > "$LOG_FILE" 2>&1 &
    local pid=$!
    echo "$pid" > "$PID_FILE"
    
    # Wait for daemon to start
    local attempts=0
    while [ $attempts -lt 30 ]; do
        if [ -S "$SOCKET_PATH" ]; then
            success "Hologramd started (PID: $pid)"
            return 0
        fi
        sleep 1
        attempts=$((attempts + 1))
    done
    
    error "Failed to start hologramd (timeout)"
    cat "$LOG_FILE"
    exit 1
}

run_tests() {
    local test_filter=${1:-}
    local env_vars=${2:-}
    
    log "Running tests..."
    
    # Set environment for tests
    export DOCKER_HOST="unix://$SOCKET_PATH"
    eval "$env_vars"
    
    cd "$TESTS_DIR"
    
    local test_cmd="go test -count=1"
    if [ -n "$test_filter" ]; then
        test_cmd="$test_cmd -run $test_filter"
    fi
    
    if ! $test_cmd; then
        error "Tests failed"
        return 1
    fi
    
    success "All tests passed"
}

case "$MODE" in
    "compat")
        log "Running in COMPAT mode (default - no Hologram fields, never fail-closed)"
        build_daemon
        start_daemon "" ""
        run_tests "" ""
        ;;
        
    "verbose")
        log "Running in VERBOSE mode (show XHologram, keeps Docker shape)"
        build_daemon
        start_daemon "1" ""
        run_tests "Verbose" "export HOLOGRAM_VERBOSE=1"
        ;;
        
    "enforce")
        log "Running in ENFORCE mode (fail-closed on bad/missing witnesses)"
        build_daemon
        start_daemon "" "1"
        run_tests "Enforce" "export HOLOGRAM_ENFORCE=1"
        ;;
        
    *)
        error "Unknown mode: $MODE"
        echo "Usage: $0 [compat|verbose|enforce]"
        exit 1
        ;;
esac

success "Test run completed successfully in $MODE mode"

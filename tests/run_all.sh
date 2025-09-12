#!/usr/bin/env bash
set -euo pipefail

# Hologram SDK Complete Test Suite Runner
# Runs all test modes and uploads artifacts

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HOLOGRAM_DIR="$SCRIPT_DIR/../hologram-sdk"
LOG_FILE="/tmp/hologramd.log"
ARTIFACTS_DIR="/tmp/hologram-artifacts"

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

# Create artifacts directory
mkdir -p "$ARTIFACTS_DIR"

# Function to collect artifacts
collect_artifacts() {
    local mode=$1
    local test_dir="$ARTIFACTS_DIR/$mode"
    mkdir -p "$test_dir"
    
    # Copy daemon logs
    if [ -f "$LOG_FILE" ]; then
        cp "$LOG_FILE" "$test_dir/hologramd.log"
        log "Collected daemon logs for $mode mode"
    fi
    
    # Copy golden files if they exist
    if [ -d "$SCRIPT_DIR/go/golden" ]; then
        cp -r "$SCRIPT_DIR/go/golden" "$test_dir/"
        log "Collected golden snapshots for $mode mode"
    fi
    
    # Copy test results if available
    if [ -f "$SCRIPT_DIR/go/test-results.json" ]; then
        cp "$SCRIPT_DIR/go/test-results.json" "$test_dir/"
    fi
}

# Function to run tests in a specific mode
run_mode() {
    local mode=$1
    log "Running tests in $mode mode..."
    
    if ! "$HOLOGRAM_DIR/run-tests.sh" "$mode"; then
        error "Tests failed in $mode mode"
        collect_artifacts "$mode"
        return 1
    fi
    
    success "Tests passed in $mode mode"
    collect_artifacts "$mode"
    return 0
}

# Main test execution
log "Starting Hologram SDK Complete Test Suite"
log "=========================================="

failed_modes=()

# Run all three modes
for mode in compat verbose enforce; do
    if ! run_mode "$mode"; then
        failed_modes+=("$mode")
    fi
done

# Summary
log ""
log "Test Suite Summary"
log "=================="

if [ ${#failed_modes[@]} -eq 0 ]; then
    success "All test modes passed!"
    log "Artifacts collected in: $ARTIFACTS_DIR"
    
    # Create summary artifact
    cat > "$ARTIFACTS_DIR/test-summary.json" << EOF
{
  "status": "success",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "modes": {
    "compat": "passed",
    "verbose": "passed", 
    "enforce": "passed"
  },
  "artifacts": [
    "compat/hologramd.log",
    "verbose/hologramd.log",
    "enforce/hologramd.log",
    "compat/golden/",
    "verbose/golden/",
    "enforce/golden/"
  ]
}
EOF
    
    exit 0
else
    error "Failed modes: ${failed_modes[*]}"
    log "Artifacts collected in: $ARTIFACTS_DIR"
    
    # Create failure summary artifact
    cat > "$ARTIFACTS_DIR/test-summary.json" << EOF
{
  "status": "failure",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "failed_modes": [$(printf '"%s",' "${failed_modes[@]}" | sed 's/,$//')],
  "artifacts": [
    "compat/hologramd.log",
    "verbose/hologramd.log", 
    "enforce/hologramd.log"
  ]
}
EOF
    
    exit 1
fi

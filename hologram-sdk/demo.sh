#!/usr/bin/env bash
set -euo pipefail

# Hologram SDK Demo - The "Cursor Aha" Moment
# Shows the progression from "It's just Docker" to "Oh wow" to "Never going back"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENGINE_DIR="$SCRIPT_DIR/engine"
SOCKET_PATH="/var/run/hologramd.sock"

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
PURPLE='\033[0;35m'
NC='\033[0m' # No Color

log() {
    echo -e "${BLUE}[$(date +'%H:%M:%S')]${NC} $1"
}

success() {
    echo -e "${GREEN}✓${NC} $1"
}

highlight() {
    echo -e "${YELLOW}✨ $1${NC}"
}

magic() {
    echo -e "${PURPLE}🔮 $1${NC}"
}

cleanup() {
    log "Cleaning up..."
    rm -f "$SOCKET_PATH"
    pkill -f hologramd || true
}

trap cleanup EXIT

# Build daemon
log "Building hologramd..."
cd "$ENGINE_DIR"
go build -o hologramd ./cmd/hologramd
success "Built successfully"

# Start daemon in background
log "Starting hologramd..."
rm -f "$SOCKET_PATH"
./hologramd --host=unix --socket-path="$SOCKET_PATH" > /tmp/hologramd-demo.log 2>&1 &
DAEMON_PID=$!

# Wait for daemon to start
sleep 3

echo ""
echo "🎬 Hologram SDK Demo - The Journey"
echo "=================================="
echo ""

# Phase 1: "It's just Docker"
echo "📦 Phase 1: 'It's just Docker'"
echo "-------------------------------"
log "Testing basic Docker compatibility..."

# Test ping
if curl -s --unix-socket "$SOCKET_PATH" http://localhost/_ping > /dev/null; then
    success "Ping works - it's just Docker!"
else
    echo "❌ Ping failed"
    exit 1
fi

# Test version
VERSION=$(curl -s --unix-socket "$SOCKET_PATH" http://localhost/version | jq -r '.Version // "unknown"')
success "Version: $VERSION - standard Docker API"

# Test images list
IMAGES=$(curl -s --unix-socket "$SOCKET_PATH" http://localhost/images/json | jq 'length')
success "Images endpoint works - found $IMAGES images"

echo ""

# Phase 2: "Oh wow" - Verbose mode
echo "🔍 Phase 2: 'Oh wow' - The Magic Revealed"
echo "----------------------------------------"
log "Enabling verbose mode to see the magic..."

# Start daemon in verbose mode
kill $DAEMON_PID 2>/dev/null || true
sleep 1
HOLOGRAM_VERBOSE=1 ./hologramd --host=unix --socket-path="$SOCKET_PATH" > /tmp/hologramd-demo.log 2>&1 &
DAEMON_PID=$!
sleep 3

# Test verbose images list
log "Checking images with verbose mode..."
VERBOSE_IMAGES=$(curl -s --unix-socket "$SOCKET_PATH" http://localhost/images/json)
if echo "$VERBOSE_IMAGES" | jq '.[0].XHologram' > /dev/null 2>&1; then
    magic "XHologram fields appear! UOR-IDs and witness status revealed!"
    echo "$VERBOSE_IMAGES" | jq '.[0].XHologram'
else
    log "No XHologram fields yet - need to pull an image"
fi

# Test verbose image pull
log "Pulling test image with verbose progress..."
PULL_OUTPUT=$(curl -s --unix-socket "$SOCKET_PATH" "http://localhost/images/create?fromImage=holo-test-ok&tag=latest")
if echo "$PULL_OUTPUT" | grep -q "XHologram"; then
    magic "XHologram progress messages in the stream!"
    echo "$PULL_OUTPUT" | grep "XHologram" | head -1
else
    log "Progress stream working, but no XHologram messages visible"
fi

echo ""

# Phase 3: "Never going back" - Enforce mode
echo "🛡️  Phase 3: 'Never going back' - Security Enforcement"
echo "----------------------------------------------------"
log "Enabling enforce mode for security..."

# Start daemon in enforce mode
kill $DAEMON_PID 2>/dev/null || true
sleep 1
HOLOGRAM_ENFORCE=1 ./hologramd --host=unix --socket-path="$SOCKET_PATH" > /tmp/hologramd-demo.log 2>&1 &
DAEMON_PID=$!
sleep 3

# Test enforce mode with bad image
log "Attempting to pull image with bad witness..."
ENFORCE_OUTPUT=$(curl -s -w "%{http_code}" --unix-socket "$SOCKET_PATH" "http://localhost/images/create?fromImage=holo-test-bad&tag=latest")
HTTP_CODE=$(echo "$ENFORCE_OUTPUT" | tail -c 4)
RESPONSE_BODY=$(echo "$ENFORCE_OUTPUT" | head -c -4)

if [ "$HTTP_CODE" = "400" ]; then
    magic "Enforce mode blocked bad witness! Security working!"
    echo "HTTP $HTTP_CODE: $RESPONSE_BODY"
else
    log "Expected 400 error, got HTTP $HTTP_CODE"
fi

# Test enforce mode with good image
log "Attempting to pull image with good witness..."
GOOD_OUTPUT=$(curl -s -w "%{http_code}" --unix-socket "$SOCKET_PATH" "http://localhost/images/create?fromImage=holo-test-ok&tag=latest")
GOOD_HTTP_CODE=$(echo "$GOOD_OUTPUT" | tail -c 4)

if [ "$GOOD_HTTP_CODE" = "200" ]; then
    success "Good witness allowed through - selective enforcement working!"
else
    log "Expected 200 success, got HTTP $GOOD_HTTP_CODE"
fi

echo ""
echo "🎉 Demo Complete!"
echo "================"
echo ""
highlight "You've seen the journey:"
echo "  1. 📦 'It's just Docker' - Perfect compatibility"
echo "  2. 🔍 'Oh wow' - Hologram magic revealed"
echo "  3. 🛡️  'Never going back' - Security enforcement"
echo ""
magic "The Hologram SDK: Docker-compatible with superpowers!"
echo ""
log "Check /tmp/hologramd-demo.log for detailed daemon output"

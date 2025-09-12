.PHONY: e2e compat verbose enforce race build clean

# Build the hologramd binary
build:
	cd hologram-sdk/engine && go build -o ../../build/hologramd ./cmd/hologramd

# Clean build artifacts
clean:
	rm -rf build/
	rm -f .pid

# End-to-end tests in compatibility mode (default)
e2e: build
	HOLOGRAM_VERBOSE= HOLOGRAM_ENFORCE= ./build/hologramd & echo $$! > .pid; sleep 2; \
	go test ./tests/go -count=1 -v; \
	kill `cat .pid` 2>/dev/null || true; rm -f .pid

# Compatibility mode tests
compat: e2e

# Verbose mode tests
verbose: build
	HOLOGRAM_VERBOSE=1 ./build/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_VERBOSE=1 go test ./tests/go -run Verbose -count=1 -v; \
	kill `cat .pid` 2>/dev/null || true; rm -f .pid

# Enforce mode tests
enforce: build
	HOLOGRAM_ENFORCE=1 ./build/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_ENFORCE=1 go test ./tests/go -run Enforce -count=1 -v; \
	kill `cat .pid` 2>/dev/null || true; rm -f .pid

# Race detector tests
race:
	go test -race ./tests/go -count=1

# Performance benchmarks
bench: build
	./build/hologramd & echo $$! > .pid; sleep 2; \
	go test -bench . -benchtime=20x ./tests/go; \
	kill `cat .pid` 2>/dev/null || true; rm -f .pid

# All tests
test-all: e2e verbose enforce race

# Help target
help:
	@echo "Available targets:"
	@echo "  build     - Build hologramd binary"
	@echo "  e2e       - Run end-to-end tests in compatibility mode"
	@echo "  compat    - Alias for e2e"
	@echo "  verbose   - Run tests with HOLOGRAM_VERBOSE=1"
	@echo "  enforce   - Run tests with HOLOGRAM_ENFORCE=1"
	@echo "  race      - Run tests with race detector"
	@echo "  bench     - Run performance benchmarks"
	@echo "  test-all  - Run all test modes"
	@echo "  clean     - Clean build artifacts"
	@echo "  help      - Show this help"

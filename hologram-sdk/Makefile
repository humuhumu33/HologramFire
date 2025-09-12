.PHONY: build e2e compat verbose enforce bench race clean test

# Build the hologramd binary
build:
	go build -o engine/cmd/hologramd/hologramd ./engine/cmd/hologramd

# Build the buildx driver
build-driver:
	go build -o tools/buildx-driver-hologram/buildx-driver-hologram ./tools/buildx-driver-hologram

# Run compatibility tests (default mode)
compat: build
	HOLOGRAM_VERBOSE= HOLOGRAM_ENFORCE= ./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_TEST=1 go test ./tests/go -count=1 -v; \
	kill `cat .pid`; rm .pid

# Run verbose mode tests
verbose: build
	HOLOGRAM_VERBOSE=1 ./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_VERBOSE=1 HOLOGRAM_TEST=1 go test ./tests/go -run Verbose -count=1 -v; \
	kill `cat .pid`; rm .pid

# Run enforce mode tests
enforce: build
	HOLOGRAM_ENFORCE=1 ./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_ENFORCE=1 HOLOGRAM_TEST=1 go test ./tests/go -run Enforce -count=1 -v; \
	kill `cat .pid`; rm .pid

# Run benchmark tests
bench: build
	./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_TEST=1 go test ./tests/go -bench . -benchtime=20x -v; \
	kill `cat .pid`; rm .pid

# Run all tests
test: build
	./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_TEST=1 go test ./tests/go -count=1 -v; \
	kill `cat .pid`; rm .pid

# Run race condition tests
race:
	go test -race ./...

# Run end-to-end tests
e2e: build
	HOLOGRAM_VERBOSE=1 HOLOGRAM_ENFORCE=1 ./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_TEST=1 go test ./tests/go -count=1 -v -run "TestContainerLifecycle|TestEventsStream|TestVolumeCreate|TestNetworkCreate|TestEnforceMode|TestVerboseImageInspect|TestVersionParity"; \
	kill `cat .pid`; rm .pid

# Clean up build artifacts
clean:
	rm -f engine/cmd/hologramd/hologramd
	rm -f tools/buildx-driver-hologram/buildx-driver-hologram
	rm -f .pid
	go clean ./...

# Install dependencies
deps:
	go mod download
	go mod tidy

# Format code
fmt:
	go fmt ./...

# Lint code
lint:
	golangci-lint run

# Run all checks
check: fmt lint race

# Docker compatibility test
docker-compat: build
	# Test that Docker client can connect to hologramd
	HOLOGRAM_VERBOSE= HOLOGRAM_ENFORCE= ./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	DOCKER_HOST=unix:///var/run/hologramd.sock docker version; \
	DOCKER_HOST=unix:///var/run/hologramd.sock docker images; \
	kill `cat .pid`; rm .pid

# Performance test
perf: build
	./engine/cmd/hologramd/hologramd & echo $$! > .pid; sleep 2; \
	HOLOGRAM_TEST=1 go test ./tests/go -bench=BenchmarkContainerStart -benchtime=100x -v; \
	kill `cat .pid`; rm .pid

# Help
help:
	@echo "Available targets:"
	@echo "  build        - Build hologramd binary"
	@echo "  build-driver - Build buildx driver"
	@echo "  compat       - Run compatibility tests"
	@echo "  verbose      - Run verbose mode tests"
	@echo "  enforce      - Run enforce mode tests"
	@echo "  bench        - Run benchmark tests"
	@echo "  test         - Run all tests"
	@echo "  race         - Run race condition tests"
	@echo "  e2e          - Run end-to-end tests"
	@echo "  clean        - Clean build artifacts"
	@echo "  deps         - Install dependencies"
	@echo "  fmt          - Format code"
	@echo "  lint         - Lint code"
	@echo "  check        - Run all checks"
	@echo "  docker-compat- Test Docker compatibility"
	@echo "  perf         - Run performance tests"
	@echo "  help         - Show this help"

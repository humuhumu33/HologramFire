# Hologram Snapshotter Makefile

.PHONY: all build test clean install docker-build docker-run

# Variables
BINARY_NAME := hologram-snapshotter
VERSION := $(shell git describe --tags --always --dirty)
BUILD_TIME := $(shell date -u '+%Y-%m-%d_%H:%M:%S')
LDFLAGS := -ldflags "-X main.version=$(VERSION) -X main.buildTime=$(BUILD_TIME)"

# Go parameters
GOCMD := go
GOBUILD := $(GOCMD) build
GOCLEAN := $(GOCMD) clean
GOTEST := $(GOCMD) test
GOGET := $(GOCMD) get
GOMOD := $(GOCMD) mod

# Directories
CMD_DIR := cmd/$(BINARY_NAME)
PKG_DIR := pkg
TESTS_DIR := tests
BUILD_DIR := build
DIST_DIR := dist

# Build targets
all: clean build test

build:
	@echo "Building $(BINARY_NAME)..."
	@mkdir -p $(BUILD_DIR)
	$(GOBUILD) $(LDFLAGS) -o $(BUILD_DIR)/$(BINARY_NAME) ./$(CMD_DIR)

build-linux:
	@echo "Building $(BINARY_NAME) for Linux..."
	@mkdir -p $(BUILD_DIR)
	GOOS=linux GOARCH=amd64 $(GOBUILD) $(LDFLAGS) -o $(BUILD_DIR)/$(BINARY_NAME)-linux-amd64 ./$(CMD_DIR)

build-darwin:
	@echo "Building $(BINARY_NAME) for macOS..."
	@mkdir -p $(BUILD_DIR)
	GOOS=darwin GOARCH=amd64 $(GOBUILD) $(LDFLAGS) -o $(BUILD_DIR)/$(BINARY_NAME)-darwin-amd64 ./$(CMD_DIR)

build-windows:
	@echo "Building $(BINARY_NAME) for Windows..."
	@mkdir -p $(BUILD_DIR)
	GOOS=windows GOARCH=amd64 $(GOBUILD) $(LDFLAGS) -o $(BUILD_DIR)/$(BINARY_NAME)-windows-amd64.exe ./$(CMD_DIR)

build-all: build-linux build-darwin build-windows

test:
	@echo "Running tests..."
	$(GOTEST) -v ./$(PKG_DIR)/...

test-integration:
	@echo "Running integration tests..."
	$(GOTEST) -v ./$(TESTS_DIR)/...

test-coverage:
	@echo "Running tests with coverage..."
	$(GOTEST) -v -coverprofile=coverage.out ./$(PKG_DIR)/...
	$(GOCMD) tool cover -html=coverage.out -o coverage.html

clean:
	@echo "Cleaning..."
	$(GOCLEAN)
	rm -rf $(BUILD_DIR)
	rm -rf $(DIST_DIR)
	rm -f coverage.out coverage.html

deps:
	@echo "Downloading dependencies..."
	$(GOMOD) download
	$(GOMOD) tidy

install: build
	@echo "Installing $(BINARY_NAME)..."
	sudo cp $(BUILD_DIR)/$(BINARY_NAME) /usr/local/bin/

# Docker targets
docker-build:
	@echo "Building Docker image..."
	docker build -t hologram-snapshotter:$(VERSION) .
	docker tag hologram-snapshotter:$(VERSION) hologram-snapshotter:latest

docker-run:
	@echo "Running Docker container..."
	docker run --rm -it --privileged hologram-snapshotter:latest

# Development targets
dev-setup:
	@echo "Setting up development environment..."
	$(GOMOD) download
	$(GOMOD) tidy
	@echo "Installing development tools..."
	$(GOGET) github.com/golangci/golangci-lint/cmd/golangci-lint@latest
	$(GOGET) github.com/securecodewarrior/gosec/v2/cmd/gosec@latest

lint:
	@echo "Running linter..."
	golangci-lint run

security:
	@echo "Running security scan..."
	gosec ./...

fmt:
	@echo "Formatting code..."
	$(GOCMD) fmt ./...

vet:
	@echo "Running go vet..."
	$(GOCMD) vet ./...

# Release targets
release: clean build-all test
	@echo "Creating release..."
	@mkdir -p $(DIST_DIR)
	cp $(BUILD_DIR)/$(BINARY_NAME)-linux-amd64 $(DIST_DIR)/
	cp $(BUILD_DIR)/$(BINARY_NAME)-darwin-amd64 $(DIST_DIR)/
	cp $(BUILD_DIR)/$(BINARY_NAME)-windows-amd64.exe $(DIST_DIR)/
	@echo "Release created in $(DIST_DIR)/"

# Documentation targets
docs:
	@echo "Generating documentation..."
	$(GOCMD) doc -all ./$(PKG_DIR) > docs/api.md

# Help target
help:
	@echo "Available targets:"
	@echo "  build          - Build the binary"
	@echo "  build-linux    - Build for Linux"
	@echo "  build-darwin   - Build for macOS"
	@echo "  build-windows  - Build for Windows"
	@echo "  build-all      - Build for all platforms"
	@echo "  test           - Run unit tests"
	@echo "  test-integration - Run integration tests"
	@echo "  test-coverage  - Run tests with coverage"
	@echo "  clean          - Clean build artifacts"
	@echo "  deps           - Download dependencies"
	@echo "  install        - Install binary to system"
	@echo "  docker-build   - Build Docker image"
	@echo "  docker-run     - Run Docker container"
	@echo "  dev-setup      - Setup development environment"
	@echo "  lint           - Run linter"
	@echo "  security       - Run security scan"
	@echo "  fmt            - Format code"
	@echo "  vet            - Run go vet"
	@echo "  release        - Create release"
	@echo "  docs           - Generate documentation"
	@echo "  help           - Show this help"

# Build stage
FROM golang:1.21-alpine AS builder

# Install build dependencies
RUN apk add --no-cache git make gcc musl-dev

# Set working directory
WORKDIR /app

# Copy go mod files
COPY go.mod go.sum ./

# Download dependencies
RUN go mod download

# Copy source code
COPY . .

# Build the binary
RUN make build-linux

# Runtime stage
FROM alpine:3.19

# Install runtime dependencies
RUN apk add --no-cache \
    fuse3 \
    ca-certificates \
    tzdata

# Create non-root user
RUN adduser -D -s /bin/sh hologram

# Set working directory
WORKDIR /app

# Copy binary from builder stage
COPY --from=builder /app/build/hologram-snapshotter-linux-amd64 /usr/local/bin/hologram-snapshotter

# Make binary executable
RUN chmod +x /usr/local/bin/hologram-snapshotter

# Create necessary directories
RUN mkdir -p /var/lib/hologram /run/hologram

# Set ownership
RUN chown -R hologram:hologram /var/lib/hologram /run/hologram

# Switch to non-root user
USER hologram

# Expose metrics port
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD /usr/local/bin/hologram-snapshotter --help || exit 1

# Default command
CMD ["/usr/local/bin/hologram-snapshotter"]

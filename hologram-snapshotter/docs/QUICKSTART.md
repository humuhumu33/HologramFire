# Hologram Snapshotter Quick Start Guide

This guide will help you get the Hologram snapshotter up and running quickly.

## Prerequisites

- Linux system with FUSE support
- Go 1.21 or later
- containerd
- nerdctl (for testing)

## Installation

### 1. Build the Snapshotter

```bash
# Clone the repository
git clone https://github.com/hologram/hologram-snapshotter.git
cd hologram-snapshotter

# Build the binary
make build

# Install to system
sudo make install
```

### 2. Configure containerd

Add the hologram snapshotter to your containerd configuration:

```bash
# Edit containerd config
sudo nano /etc/containerd/config.toml
```

Add the following section:

```toml
[plugins."io.containerd.snapshotter.v1.hologram"]
  root_path = "/var/lib/containerd/hologram"
```

### 3. Restart containerd

```bash
sudo systemctl restart containerd
```

## Basic Usage

### Test with nerdctl

```bash
# Pull an image using hologram snapshotter
nerdctl --snapshotter=hologram pull alpine:3.19

# Run a container
nerdctl --snapshotter=hologram run --rm alpine:3.19 echo "Hello Hologram"
```

### Test with Docker

```bash
# Pull and run as usual (Docker will use containerd with hologram snapshotter)
docker pull alpine:3.19
docker run --rm alpine:3.19 echo "Hello Hologram"
```

## Environment Configuration

### Enable Verbose Mode

```bash
export HOLOGRAM_VERBOSE=1
```

This will add detailed logging and metadata to operations.

### Enable Enforce Mode

```bash
export HOLOGRAM_ENFORCE=1
```

This will cause operations to fail if witness verification fails.

### Configure CTP-96 Endpoint

```bash
export HOLOGRAM_CTP96_ENDPOINT=http://your-ctp96-server:8080
```

### Configure Witness Endpoint

```bash
export HOLOGRAM_WITNESS_ENDPOINT=http://your-witness-server:8081
```

## Verification

### Check Snapshotter Registration

```bash
# Check if hologram snapshotter is available
nerdctl --snapshotter=hologram info
```

### Monitor Operations

```bash
# Check containerd logs
journalctl -u containerd -f

# Check metrics (if enabled)
curl http://localhost:8080/metrics
```

## Troubleshooting

### Common Issues

1. **"snapshotter not found"**
   - Ensure containerd is configured with hologram snapshotter
   - Restart containerd after configuration changes

2. **"FUSE not available"**
   - Install fuse3 package: `sudo apt-get install fuse3`
   - Ensure user has FUSE permissions

3. **"Permission denied"**
   - Check file permissions in `/var/lib/containerd/hologram`
   - Ensure containerd user has access

### Debug Mode

Enable debug logging:

```bash
export HOLOGRAM_VERBOSE=1
export CONTAINERD_LOG_LEVEL=debug
```

## Next Steps

- Read the [full documentation](README.md)
- Explore [advanced configuration](CONFIGURATION.md)
- Check out [performance tuning](PERFORMANCE.md)
- Learn about [monitoring](MONITORING.md)

# Example 2: Provenance On

**"Oh wow" moment - UOR-ID + witness verification**

This example demonstrates the first "aha moment" by enabling Hologram's provenance features. You'll see UOR-IDs and witness verification in action.

## Prerequisites

1. Complete Example 1 first
2. Ensure hologramd is running with UOR features enabled

## Running the Example

```bash
# Enable verbose mode to see Hologram fields
export HOLOGRAM_VERBOSE=1

# Create a buildx builder with hologram driver
docker buildx create --use --name hologram

# Build an image with hologram driver (this would be implemented in buildx driver)
docker buildx build --driver=hologram -t app:holo .

# Inspect the image to see XHologram fields
docker inspect app:holo | jq '.[0].XHologram'

# Pull an image and see provenance information
docker pull nginx:alpine
docker images  # Shows XHologram fields when verbose is enabled
```

## What You'll See

With `HOLOGRAM_VERBOSE=1`:

```json
{
  "XHologram": {
    "uor_id": "uor:sha256:deadbeef1234567890abcdef1234567890abcdef1234567890abcdef1234567890",
    "witness_ok": true,
    "build_provenance": {
      "builder": "hologram",
      "timestamp": "2024-01-01T00:00:00Z",
      "witness_bundle": "ccm_hash:abc123..."
    }
  }
}
```

During image pull, you'll see an extra progress line:
```json
{"status":"XHologram","uor_id":"uor:...","witness_ok":true}
```

## Key Points

- **Provenance tracking**: Every image gets a UOR-ID
- **Witness verification**: Cryptographic proof of integrity
- **Opt-in visibility**: Only shown when `HOLOGRAM_VERBOSE=1`
- **Docker compatibility**: Standard Docker commands still work
- **Build integration**: Works with buildx drivers

## The "Aha" Moment

This is where users realize Hologram isn't just Docker compatibility - it's Docker with **provenance superpowers**. Every image is cryptographically verified and tracked, but it's completely invisible unless you explicitly enable verbose mode.

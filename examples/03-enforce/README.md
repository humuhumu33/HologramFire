# Example 3: Enforce Mode

**"Never going back" moment - Fail-closed security**

This example demonstrates Hologram's enforcement capabilities. When `HOLOGRAM_ENFORCE=1` is set, operations fail if witness verification fails, providing fail-closed security.

## Prerequisites

1. Complete Examples 1 and 2
2. Understand the difference between warning and enforcement modes

## Running the Example

```bash
# First, see what happens in warning mode (default)
docker run --rm nginx:alpine echo "This works even with invalid witness"

# Now enable enforce mode
export HOLOGRAM_ENFORCE=1

# Try to run a container with invalid witness
docker run --rm nginx:alpine echo "This should fail if witness is invalid"

# The operation will fail with:
# {"message": "artifact witness invalid or missing"}
```

## What You'll See

### Warning Mode (Default)
- Operations succeed even with invalid witnesses
- Warnings are logged but don't block execution
- Compatible with existing workflows

### Enforce Mode (`HOLOGRAM_ENFORCE=1`)
- Operations fail if witness verification fails
- Clear error messages in Docker format
- Fail-closed security policy

Example error response:
```json
{
  "message": "artifact witness invalid or missing"
}
```

With verbose mode enabled, you'll also see:
```json
{
  "message": "artifact witness invalid or missing",
  "XHologram": {
    "error_context": "hologram_enforcement",
    "enforce_mode": true
  }
}
```

## Key Points

- **Fail-closed security**: Invalid witnesses block execution
- **Opt-in enforcement**: Only active when `HOLOGRAM_ENFORCE=1`
- **Docker-compatible errors**: Standard error format
- **Gradual adoption**: Start with warnings, enable enforcement when ready
- **Production ready**: Enforce mode for security-critical environments

## The "Never Going Back" Moment

This is where users realize they can have **cryptographic guarantees** about their container images. No more "trust but verify" - with enforce mode, you get "verify or fail". This level of security assurance is impossible with standard Docker.

## Use Cases

- **CI/CD pipelines**: Ensure only verified images are deployed
- **Production environments**: Block unverified containers
- **Compliance requirements**: Meet security standards
- **Supply chain security**: Prevent compromised images from running

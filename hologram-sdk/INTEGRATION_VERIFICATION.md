# Hologram Integration Verification

This document describes the integration verification matrix for locking the Hologram Blueprint (atlas-12288, UOR, VPI, CTP-96, profiles, acceptance artifacts) while maintaining Docker SDK UX compatibility.

## Integration Verification Matrix

| Docker Surface (unchanged)                          | Hologram Module (internal)                    | What to verify now                            | How to expose (only if verbose)             |
| --------------------------------------------------- | --------------------------------------------- | --------------------------------------------- | ------------------------------------------- |
| `/images/create`, `/images/json`                    | `images/resolver` (tag→UOR), `images/witness` | Resolve tag→UOR-ID; if bundle present, verify | `XHologram: { "uor_id", "witness_ok" }`     |
| `/containers/*` (create/start/inspect/logs/stop/rm) | `runtime/lease` (VPI)                         | Allocate `lease_id`; track budget/energy      | `XHologram: { "lease_id", "budget_delta" }` |
| `/networks/*` (bridge default)                      | `networks/ctp96` (opt-in)                     | Bridge works as Docker; CTP-96 gated          | `XHologram: { "ctp96_session" }`            |
| `/events`                                           | `events/bus`                                  | Emit Docker-shaped events                     | `Actor.Attributes["XHologram.*"]`           |
| Policies (no API change)                            | `blueprint/profiles`, `enforce`               | Profiles active; fail-closed is opt-in        | via env: `HOLOGRAM_ENFORCE=1`               |

## Quickstart (Unchanged Docker UX)

### Basic Usage

```bash
# Start hologramd (same as dockerd)
export DOCKER_HOST=unix:///var/run/hologramd.sock

# All Docker commands work unchanged
docker version
docker images
docker pull nginx:alpine
docker run --rm nginx:alpine echo "hello"
```

### Hologram Mode (Optional)

```bash
# Build with Hologram features
docker buildx build --driver=hologram -t app:holo .

# Run with enforcement
HOLOGRAM_ENFORCE=1 docker run app:holo

# Observe Hologram fields
HOLOGRAM_VERBOSE=1 docker inspect app | jq '.[].XHologram'
```

## Environment Variables

### Verbose Gating (Hide Hologram fields by default)

```bash
# Show XHologram fields in responses
export HOLOGRAM_VERBOSE=1
```

### Enforce Mode (Fail-closed is opt-in)

```bash
# Enable fail-closed policy
export HOLOGRAM_ENFORCE=1
```

### Profiles (Internal policy gate)

```bash
# Set conformance profile
export HOLOGRAM_PROFILE=P-Network  # P-Core, P-Network, P-Runtime, P-Full
```

## Blueprint Self-Test

```bash
# Run blueprint acceptance tests
hologramd --selftest

# Test specific profile
HOLOGRAM_PROFILE=P-Full hologramd --selftest
```

## SDK Compatibility

### Go SDK

```go
cli, _ := client.NewClientWithOpts(client.WithHost("unix:///var/run/hologramd.sock"))
v, _ := cli.ServerVersion(ctx)
imgs, _ := cli.ImageList(ctx, types.ImageListOptions{})
r, _ := cli.ImagePull(ctx, "nginx:alpine", types.ImagePullOptions{})
io.Copy(io.Discard, r)
```

### Node SDK

```js
const Docker = require('dockerode');
const docker = new Docker({ socketPath: '/var/run/hologramd.sock' });
console.log(await docker.ping());
console.log(await docker.listImages());
```

## API Response Examples

### Standard Mode (Docker Compatible)

```json
{
  "Id": "sha256:...",
  "RepoTags": ["nginx:alpine"],
  "Created": 1234567890,
  "Size": 1024,
  "VirtualSize": 1024,
  "Labels": {}
}
```

### Verbose Mode (With XHologram)

```json
{
  "Id": "sha256:...",
  "RepoTags": ["nginx:alpine"],
  "Created": 1234567890,
  "Size": 1024,
  "VirtualSize": 1024,
  "Labels": {},
  "XHologram": {
    "uor_id": "uor:sha256:...",
    "witness_ok": true
  }
}
```

## CI Integration

The integration verification includes:

- **Matrix Tests**: Run parity tests against both `dockerd` and `hologramd`
- **Self-Test**: Blueprint acceptance tests via `hologramd --selftest`
- **Environment Tests**: Verify `HOLOGRAM_VERBOSE=1` and `HOLOGRAM_ENFORCE=1` behavior
- **SDK Tests**: Go and Node.js SDK compatibility tests
- **Performance Tests**: Regression testing for API response times

## Definition of Done

✅ All endpoints implemented return byte-compatible Docker shapes (no Hologram keys unless verbose)  
✅ Each request path has internal mapping to resolver/witness/lease modules  
✅ Failure policy only active with `HOLOGRAM_ENFORCE=1`  
✅ Parity harness passes against dockerd  
✅ CI runs `--selftest`  
✅ Docs show unchanged UX; Hologram features are a toggle, not a new API  

## Troubleshooting

### XHologram fields not appearing

```bash
# Check verbose mode is enabled
export HOLOGRAM_VERBOSE=1
curl -H "X-Hologram-Verbose: true" unix:///var/run/hologramd.sock/images/json
```

### Enforce mode not working

```bash
# Check enforce mode is enabled
export HOLOGRAM_ENFORCE=1
# Verify in logs that enforce mode is active
```

### Profile not applying

```bash
# Check profile setting
export HOLOGRAM_PROFILE=P-Network
# Verify profile in server info
curl unix:///var/run/hologramd.sock/info | jq '.SystemStatus'
```

## Architecture

The integration maintains Docker compatibility through:

1. **Verbose Gating**: `maybeAttachXHologram()` function conditionally adds Hologram fields
2. **Enforce Mode**: `blueprint.Enforce()` enables fail-closed policies
3. **Profile System**: `blueprint.CurrentProfile()` gates optional features
4. **Acceptance Hooks**: `blueprint.SelfTest()` validates Blueprint conformance
5. **UOR Mapping**: Image pull resolves to UOR-ID and verifies witnesses
6. **Docker Shape**: All responses maintain Docker-compatible structure

This ensures that hologramd is a drop-in replacement for dockerd while providing optional Hologram features when explicitly enabled.

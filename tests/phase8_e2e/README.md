# Phase 8 - End-to-End (Publisher → Marketplace → Install → Use)

This phase tests the complete flow from publishing a manifest to IPFS, registering it in the GraphQL marketplace, installing it, and using it. **Now with auditability, idempotency, and CI-friendly features!**

## Prerequisites

1. **IPFS Node**: Set `IPFS_API` environment variable (e.g., `http://127.0.0.1:5001`)
2. **GraphQL Server**: Set `GRAPHQL_URL` environment variable (e.g., `http://localhost:4000/graphql`)
3. **Optional**: Set `E2E_APP_NAME` to customize the app name used in tests

## Running Phase 8

```bash
# Set up environment
export IPFS_API=http://127.0.0.1:5001
export GRAPHQL_URL=http://localhost:4000/graphql
export E2E_APP_NAME=demo/app/hello

# Run E2E tests
python -m pytest -m phase8_e2e -v

# View audit artifacts
cat reports/e2e/events.jsonl

# Or use make (if available)
make phase8
```

## What It Tests

### IPFS-Only Path
- **Idempotent**: Auto-generates unique app names with UUID suffixes to prevent collisions
- **Tamper-resistant**: Verifies embedded SHA256 matches manifest content before publish
- **Tamper-negative**: Proves CID changes when manifest bytes change (1-byte flip test)
- Publishes manifest to IPFS and verifies with `cat`
- Validates manifest structure

### GraphQL Marketplace Path
- **Auditable**: All operations logged to `reports/e2e/events.jsonl` with timestamps
- Registers the IPFS CID in the marketplace (tries multiple mutation names)
- Attempts to install the app (gracefully skips if not supported)
- Resolves the app by name to get its encoding
- **Cleanup**: Optional uninstall test for safe cleanup

## Tolerant Design

The tests are designed to work with different GraphQL schemas by trying common operation names:

**Publish mutations tried:**
- `publishApp(cid,name)`
- `marketplacePublish(cid,name)`
- `upsertService(cid,name)`

**Install mutations tried:**
- `installApp(name)`
- `installByCid(cid)`
- `appsInstall(name)`

**Resolve query:**
- `resolve(name) { encoding }`

## Generated Artifacts

- `demo.manifest.json` - Generated manifest for testing (with unique names)
- `reports/e2e/events.jsonl` - **JSONL audit log** with all operations, CIDs, and responses
- Test results show which GraphQL operations succeeded

## CI/CD Integration

- **GitHub Actions**: `.github/workflows/e2e.yml` runs E2E tests when secrets are present
- **Secrets required**: `GRAPHQL_URL` and `IPFS_API` 
- **Artifacts uploaded**: E2E event logs are preserved as build artifacts
- **Conditional execution**: Only runs when both secrets are configured

## Quick Triage Tools

- **Artifact Summary**: `python scripts/summarize_e2e.py` - Shows event counts and latest operations
- **Search Discovery**: Tests include optional marketplace search verification
- **Security**: Artifact logging includes redaction guidance for sensitive data

## Graceful Degradation

- If IPFS is not available, IPFS tests are skipped
- If GraphQL is not available, marketplace tests are skipped
- If install mutations don't exist, the test continues to resolve step
- If uninstall mutations don't exist, cleanup is skipped (logged)
- Tests pass as long as the core publish → resolve flow works

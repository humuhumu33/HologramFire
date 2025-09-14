# Phase 6: Performance SLOs

This phase benchmarks **real production code** only (no mocks), writes **CSV artifacts** for CI, and gates on **p95 thresholds** that can be tuned via environment variables.

## What This Measures

### Atlas Core (if exported by your build):
- `verify(state)` p95 target (default **< 10 ms**)
- `encode(data)` p95 target (default **< 100 ms** for 1 MB)

### GraphQL Resolvers:
- `resolve(name)` p95 target (default **< 100 ms**, configurable)

If `atlas encode/verify` aren't available in your TS build, the tests **skip** gracefully.

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `SLO_ENCODE_P95_MS` | 100 | p95 threshold for encode operations (ms) |
| `SLO_VERIFY_P95_MS` | 10 | p95 threshold for verify operations (ms) |
| `SLO_GQL_P95_MS` | 100 | p95 threshold for GraphQL resolve (ms) |
| `ENC_MB` | 1 | Payload size for encode test (MB) |
| `GQL_SAMPLES` | 40 | Number of GraphQL samples to collect |
| `GQL_WARMUP` | 5 | Number of GraphQL warmup runs |
| `GRAPHQL_TEST_NAME` | demo/object/alpha | Test name for GraphQL resolution |

## Running Tests

```bash
# Ensure prod build is present (for atlas tests)
pnpm -C core build

# Run with default SLOs
make phase6

# Quick test with relaxed thresholds (dev laptop)
make phase6-fast

# View performance artifacts
make perf-report
```

## Artifacts

Performance data is written to CSV files in `reports/perf/`:
- `core_perf.csv` - Atlas encode/verify performance
- `graphql_perf.csv` - GraphQL resolver performance

Each CSV includes p50, p95, p99, average, sample count, and notes for trend analysis.

## CI Integration

For CI environments, you can:
1. Set stricter thresholds via environment variables
2. Commit baseline CSVs from main branch
3. Diff performance trends in CI (simple GitHub Action step)
4. Gate deployments on p95 thresholds

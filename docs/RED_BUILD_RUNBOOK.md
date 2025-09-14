# 🚨 Red Build Runbook - Fast Triage

When your CI pipeline fails, use this runbook for rapid diagnosis and resolution.

## 🔍 Quick Diagnosis

### 1. Check CI Job Summary
- Open the GitHub Actions run
- Look at the job summary for key metrics
- Check which step failed and why

### 2. Download Artifacts
- Download `hologram-reports-{type}` artifact
- Extract and open `reports/index.html`
- Check `reports/e2e/events.jsonl` for E2E status

## 🚨 Perf Gate Failed

### Symptoms
- CI step "Perf Gate" failed with exit code 1
- Error message shows budget violations

### Triage Steps

#### 1. Check Performance Data
```bash
# Open reports/index.html and look at "Best p95 per metric" table
# Note which metrics exceeded budgets
```

#### 2. Compare with Baseline
```bash
# Check if this is a regression vs. previous runs
# Look for >10% increase in p95 values
```

#### 3. Local Reproduction
```bash
# Set very high budgets to confirm parsing works
SLO_VERIFY_P95_MS=1000 SLO_ENCODE_P95_MS=1000 SLO_GQL_P95_MS=1000 python scripts/check_perf_budget.py

# Run performance tests locally
python -m pytest -m phase6_perf -v
```

#### 4. Common Causes & Solutions

| Cause | Solution |
|-------|----------|
| **Infrastructure issues** | Check CPU/memory usage, network latency |
| **Code regression** | Review recent changes, check for new bottlenecks |
| **Test environment** | Verify test data size, network conditions |
| **SLO too strict** | Consider adjusting budgets if consistently failing |

### Resolution
1. **If infrastructure**: Restart services, check resource usage
2. **If code regression**: Revert or optimize the problematic change
3. **If test environment**: Fix test setup, data, or network issues
4. **If SLO adjustment needed**: Update budgets in CI configuration

## 🚨 E2E Tests Failed

### Symptoms
- CI step "E2E Tests" failed
- No E2E events in `events.jsonl` or incomplete pipeline

### Triage Steps

#### 1. Check Event Log
```bash
# Look at reports/e2e/events.jsonl
# Find the last successful event
# Identify where the pipeline broke
```

#### 2. Common Failure Points

| Failure Point | Symptoms | Solutions |
|---------------|----------|-----------|
| **IPFS Publish** | No `ipfs_publish` event | Check IPFS_API, daemon running, ports open |
| **Marketplace Publish** | No `marketplace_publish` event | Check GraphQL_URL, schema, mutations |
| **Install** | No `install` event | Check GraphQL mutations, app name |
| **Resolve** | No `resolve` event or empty encoding | Check GraphQL queries, content availability |

#### 3. Service Health Checks
```bash
# Check IPFS
curl -X POST http://127.0.0.1:5001/api/v0/version

# Check GraphQL
curl -X POST http://localhost:4000/graphql \
  -H "Content-Type: application/json" \
  -d '{"query": "{ __schema { types { name } } }"}'
```

#### 4. Local Reproduction
```bash
# Set environment variables
export IPFS_API=http://127.0.0.1:5001
export GRAPHQL_URL=http://localhost:4000/graphql
export E2E_APP_NAME=demo/app/hello

# Run E2E tests
python -m pytest -m phase8_e2e -v
```

### Resolution
1. **If IPFS issues**: Restart IPFS daemon, check ports, verify API
2. **If GraphQL issues**: Check schema, mutations, queries, server status
3. **If app name issues**: Verify E2E_APP_NAME matches available apps
4. **If network issues**: Check connectivity, firewall, DNS

## 🚨 Baseline Comparison Failed

### Symptoms
- CI step "Baseline Comparison" failed
- Error message shows performance regression

### Triage Steps

#### 1. Check Regression Details
```bash
# Look at the error message for specific metrics and percentages
# Note which metrics regressed and by how much
```

#### 2. Compare with Previous Runs
```bash
# Check if this is a consistent regression or one-off
# Look at recent performance trends
```

#### 3. Local Analysis
```bash
# Run baseline comparison locally
python scripts/baseline_compare.py

# Check if baseline exists
ls -la reports/perf/baseline.json
```

### Resolution
1. **If consistent regression**: Investigate code changes, infrastructure
2. **If one-off**: Check for temporary issues, retry the build
3. **If baseline missing**: Ensure baseline is saved on main branch
4. **If threshold too strict**: Consider adjusting REGRESSION_THRESHOLD_PCT

## 🚨 No Performance Data

### Symptoms
- Empty CSV files in `reports/perf/`
- "No performance data found" messages

### Triage Steps

#### 1. Check Phase 6 Tests
```bash
# Verify Phase 6 tests ran successfully
python -m pytest -m phase6_perf -v
```

#### 2. Check Test Output
```bash
# Look for CSV generation in test output
# Check if tests are actually running
```

#### 3. Check Test Configuration
```bash
# Verify test markers and configuration
# Check if performance tests are enabled
```

### Resolution
1. **If tests not running**: Check test markers, configuration
2. **If CSV not generated**: Check test implementation, file permissions
3. **If tests failing**: Fix test issues, dependencies, environment

## 🚨 Missing E2E Events

### Symptoms
- Empty `events.jsonl` file
- No E2E events in reports

### Triage Steps

#### 1. Check E2E Test Execution
```bash
# Verify E2E tests ran
python -m pytest -m phase8_e2e -v
```

#### 2. Check Environment Variables
```bash
# Verify required secrets are set
echo $IPFS_API
echo $GRAPHQL_URL
echo $E2E_APP_NAME
```

#### 3. Check Service Availability
```bash
# Test service connectivity
curl -X POST $IPFS_API/api/v0/version
curl -X POST $GRAPHQL_URL -H "Content-Type: application/json" -d '{"query": "{ __schema { types { name } } }"}'
```

### Resolution
1. **If secrets missing**: Set required environment variables
2. **If services down**: Start IPFS daemon, GraphQL server
3. **If tests failing**: Fix test implementation, dependencies

## 🔧 Emergency Procedures

### Skip Performance Gating (Temporary)
```bash
# In CI, temporarily add || true to perf gate step
run: python scripts/check_perf_budget.py || true
```

### Skip E2E Tests (Temporary)
```bash
# In CI, comment out E2E test step
# - name: E2E Tests
#   run: python -m pytest -m phase8_e2e -q
```

### Force Baseline Update
```bash
# Manually update baseline (use with caution)
python scripts/baseline_compare.py
```

## 📞 Escalation

### When to Escalate
- Multiple consecutive failures
- Infrastructure issues affecting multiple services
- Performance regressions >50%
- E2E failures affecting production deployments

### Who to Contact
- **Performance issues**: Platform/DevOps team
- **E2E failures**: Backend/API team
- **Infrastructure issues**: Infrastructure team
- **Test failures**: QA/Testing team

## 🎯 Prevention

### Best Practices
1. **Monitor trends**: Watch for gradual performance degradation
2. **Test locally**: Always test changes locally before pushing
3. **Review baselines**: Regularly review and update performance baselines
4. **Service health**: Monitor IPFS and GraphQL service health
5. **Documentation**: Keep runbook updated with new failure patterns

### Proactive Monitoring
- Set up alerts for CI failures
- Monitor performance trends over time
- Track E2E success rates
- Watch for infrastructure issues

This runbook should help you quickly diagnose and resolve most CI failures. Keep it updated as you encounter new failure patterns! 🚀

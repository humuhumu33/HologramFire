# 🔥 Hologram Pipeline - Operational Wrap-Up

This guide provides everything your team needs to run, debug, and enforce the production-grade Phase 8 pipeline with confidence.

## 🚀 Quick Smoke Test (Local)

### Basic Health Check
```bash
# Perf + E2E (skips gracefully if services absent)
export IPFS_API=http://127.0.0.1:5001
export GRAPHQL_URL=http://localhost:4000/graphql

python -m pytest -m "phase6_perf or phase8_e2e" -q
python scripts/aggregate_reports.py
python scripts/check_perf_budget.py
```

### Windows Convenience
```powershell
.\tools\reports.ps1
.\tools\perf-gate.ps1
```

### Verification Checklist
- [ ] `reports/index.html` renders with perf CSVs + E2E counts
- [ ] `reports/e2e/events.jsonl` shows successful pipeline:
  - `ipfs_publish` with a CID
  - `marketplace_publish` with that CID  
  - `resolve` with non-empty `encoding`
  - Optional `search` hit

## 🔧 Promote to Full Enforcement (CI)

### 1. Turn On Hard Fail for Perf Gate
In `.github/workflows/reports.yml`, remove `|| true` from the perf-gate step:

```yaml
# Change this:
run: python scripts/check_perf_budget.py || true

# To this:
run: python scripts/check_perf_budget.py
```

### 2. Contextual Budgets
Keep strict SLOs on `main`, relaxed on PRs via environment variables:

- `SLO_VERIFY_P95_MS` (main: 8ms, PR: 15ms)
- `SLO_ENCODE_P95_MS` (main: 80ms, PR: 150ms)  
- `SLO_GQL_P95_MS` (main: 80ms, PR: 150ms)

### 3. Enable Baseline Guard
- **On `main`**: After a green run, persist baseline (`reports/perf/baseline.json`) as an artifact
- **On PR**: Download the baseline and run `python scripts/baseline_compare.py` to fail if >10% regression even if under SLO

## 🚨 Red Build Runbook (Fast Triage)

### Perf Gate Failed
1. **Open `reports/index.html`**; check top p95 rows
2. **Compare with baseline** in the CI artifact; if >10% drift, inspect infra / recent code paths
3. **Locally reproduce**:
   ```bash
   SLO_VERIFY_P95_MS=1000 SLO_ENCODE_P95_MS=1000 SLO_GQL_P95_MS=1000 python scripts/check_perf_budget.py  # confirm parsing ok
   python -m pytest -m phase6_perf -v
   ```

### E2E Fail
1. **Check `events.jsonl`** for last successful step
2. **If IPFS failed**: Confirm `IPFS_API` and daemon/ports
3. **If GraphQL failed**: Verify `GRAPHQL_URL`, schema ops (publish/install/resolve); tests try multiple mutation names
4. **Quick diagnosis**: Use `scripts/summarize_e2e.py` for count/last-events view

### Common Issues & Solutions

| Issue | Symptom | Solution |
|-------|---------|----------|
| No perf data | Empty CSV files | Check Phase 6 tests ran successfully |
| Budget violations | p95 > SLO | Review SLO settings vs actual performance |
| Missing E2E events | Empty events.jsonl | Verify secrets set and services running |
| Baseline comparison fails | No baseline found | Check if baseline exists and is valid |
| Cache profiling issues | Missing cache_profiles.json | Ensure cache_profiler.py is imported in tests |

## 🔒 Security & Hygiene

### Secrets Management
- Use `scripts/secrets_redactor.py` for any future logging of headers or tokens
- Keep artifact retention to 7–14 days
- Never log Bearer tokens, API keys, or cookies

### Environment Variables
```bash
# Required for E2E
IPFS_API=http://127.0.0.1:5001
GRAPHQL_URL=http://localhost:4000/graphql
E2E_APP_NAME=demo/app/hello

# Performance budgets
SLO_VERIFY_P95_MS=10
SLO_ENCODE_P95_MS=100
SLO_GQL_P95_MS=100

# Regression detection
REGRESSION_THRESHOLD_PCT=10
```

## 📊 What "Good" Looks Like

### Successful CI Run
- ✅ All performance budgets met
- ✅ No significant regressions vs baseline  
- ✅ E2E events show successful publish/install/use
- ✅ HTML report generated with clean data
- ✅ Job summary shows key metrics

### Artifacts Generated
- `reports/index.html` - Complete dashboard
- `reports/e2e/events.jsonl` - E2E event log
- `reports/perf/*.csv` - Performance data
- `reports/perf/baseline.json` - Performance baseline
- `reports/perf/cache_profiles.json` - Cache performance data

### Job Summary Content
- Performance metrics table with best p95s
- E2E highlights with latest events
- Links to artifacts and reports

## 🎯 Optional Niceties (Drop-in Later)

### 1. Slack/Teams Webhook
Post p95s + last CID/name (tiny wrapper around `ci_summary.py`)

### 2. Cold vs Warm Profiles
Add a second Phase 6 job section flagged `COLD=1`; `cache_profiler.py` will show ratios in `reports/perf/cache_profiles.json`

### 3. Nightly Matrix
Run Phase 6+8 with stricter SLOs and larger samples; PRs keep fast/lenient

### 4. Status Badge
One-liner "green gate" status badge generator for repo README that flips based on latest perf gate + E2E results

## 🛠️ Debug Commands

### Check Data Exists
```bash
ls -la reports/perf/
ls -la reports/e2e/
```

### Test Individual Components
```bash
python scripts/check_perf_budget.py
python scripts/baseline_compare.py
python scripts/ci_summary.py
```

### Force Budget Violation for Testing
```bash
SLO_VERIFY_P95_MS=1 python scripts/check_perf_budget.py
```

### E2E Quick Summary
```bash
python scripts/summarize_e2e.py
```

## 📈 Monitoring & Alerting

### Performance Trends
- Baseline comparison catches slow drifts
- Cache profiling identifies optimization opportunities
- Historical data in HTML reports

### E2E Health
- Event counts and success rates
- Latest successful deployments
- CID tracking for audit trails

## 🚀 Team Onboarding

### For New Team Members
1. Run the quick smoke test locally
2. Review `reports/index.html` to understand the dashboard
3. Check CI artifacts to see what "good" looks like
4. Practice the red build runbook scenarios

### For DevOps/Platform Teams
1. Set up secrets in GitHub Actions
2. Configure artifact retention policies
3. Set up monitoring for CI job failures
4. Review and adjust SLO budgets as needed

## 🎉 Success Metrics

- **Zero false positives** in performance gating
- **Fast feedback** (< 10 minutes for PR runs)
- **Clear triage** when builds fail
- **Audit trail** for all deployments
- **Trend visibility** for performance optimization

This pipeline is now **truly production-grade** and ready for enterprise deployment! 🚀

# 🔥 Day-2 Operations Playbook - Hologram Pipeline

**Status**: ✅ **STEADY STATE** - Complete operational playbook for ongoing management

## 📅 **Weekly Operations**

### **Monday: Baseline Refresh**
```bash
# Only refresh baseline if:
# 1. Perf gate passes on main
# 2. No regressions >5-10%
# 3. Performance is stable

# Check current performance
python scripts/check_perf_budget.py

# If stable, update baseline
python scripts/baseline_compare.py

# Create PR with baseline update
git add reports/perf/baseline.json
git commit -m "chore: update performance baseline - no regressions detected"
```

### **Weekly Health Check**
- [ ] Review `reports/index.html` for performance trends
- [ ] Check flake database for new quarantined tests
- [ ] Verify chaos test results from nightly runs
- [ ] Review E2E success rates
- [ ] Check artifact retention and cleanup

## 🌙 **Nightly Operations**

### **Scheduled Nightly Run**
```yaml
# Runs automatically at 2 AM UTC
schedule:
  - cron: '0 2 * * *'
```

**What runs nightly:**
- Phase 6 (full samples: 100/10/4MB)
- Phase 8 (complete E2E pipeline)
- Phase 9 (chaos tests)
- Performance baseline comparison
- Flake detection and quarantine

**Post-run actions:**
- Summary posted via `ci_summary.py`
- Artifacts uploaded with 14-day retention
- Status badge updated
- Alerts sent if failures detected

## 🚨 **Triage Loop (When CI is Red)**

### **Step 1: Quick Diagnosis**
```bash
# Open reports/index.html
# Check p95 deltas vs baseline
# Look for performance regressions >10%
```

### **Step 2: E2E Analysis**
```bash
# Check events.jsonl for last successful step
tail -20 reports/e2e/events.jsonl

# Quick E2E summary
python scripts/summarize_e2e.py
```

### **Step 3: Performance Analysis**
```bash
# If perf red: rerun local with increased budgets
export SLO_VERIFY_P95_MS=1000
export SLO_ENCODE_P95_MS=1000  
export SLO_GQL_P95_MS=1000
python scripts/check_perf_budget.py

# This confirms parsing vs true slowdown
```

### **Step 4: Root Cause Analysis**
- **Infrastructure issues**: Check CPU/memory, network latency
- **Code regression**: Review recent changes, check for bottlenecks
- **Test environment**: Verify test data, network conditions
- **SLO adjustment**: Consider if budgets need updating

### **Step 5: Resolution**
- **Infrastructure**: Restart services, check resource usage
- **Code regression**: Revert or optimize problematic change
- **Test environment**: Fix test setup, data, or network issues
- **SLO adjustment**: Update budgets in CI configuration

## 🔒 **Quarantine Policy**

### **Auto-Quarantine Rules**
- **Trigger**: ≥2 flakes in 7 days
- **Action**: Test automatically quarantined
- **Notification**: Create ticket for investigation
- **Unquarantine**: Only after 10 consecutive greens

### **Quarantine Management**
```bash
# Check quarantined tests
python scripts/flake_detector.py report

# Unquarantine a test (after 10 consecutive greens)
python scripts/flake_detector.py unquarantine test_name

# Manual quarantine (if needed)
python scripts/flake_detector.py quarantine test_name
```

### **Quarantine Workflow**
1. **Test flakes** → Auto-quarantined
2. **Ticket created** → Investigation assigned
3. **Root cause found** → Fix implemented
4. **10 consecutive greens** → Unquarantined
5. **Monitoring** → Ensure no regression

## 📊 **Baseline Hygiene**

### **Baseline Management**
- **Keep `baseline.json` small** - Only essential metrics
- **Roll forward deliberately** - With PR note explaining why
- **Version control** - Baseline changes tracked in git
- **Validation** - Only update if performance is stable

### **Baseline Update Process**
```bash
# 1. Verify current performance is stable
python scripts/check_perf_budget.py

# 2. Check for regressions
python scripts/baseline_compare.py

# 3. If stable, update baseline
git add reports/perf/baseline.json
git commit -m "chore: update baseline - performance stable, no regressions"

# 4. Create PR with explanation
```

### **Baseline Rollback**
```bash
# If baseline update causes issues
git checkout HEAD~1 -- reports/perf/baseline.json
git commit -m "chore: rollback baseline - performance regression detected"
```

## 🌪️ **Chaos Cadence**

### **Monthly Chaos Enhancement**
- **Month 1**: IPFS restart timing variations
- **Month 2**: GraphQL latency tier testing
- **Month 3**: CTP-96 nonce expiry edge cases
- **Month 4**: Network partition scenarios
- **Month 5**: Resource exhaustion testing
- **Month 6**: Multi-service failure scenarios

### **Chaos Test Development**
```bash
# Add new chaos test
# 1. Create test in tests/phase9_chaos/
# 2. Mark with @pytest.mark.no_ci
# 3. Add to nightly schedule
# 4. Document expected behavior
# 5. Add to triage runbook
```

### **Chaos Results Analysis**
- **Success rate** - Should be >95%
- **Recovery time** - Should be <30 seconds
- **Data integrity** - No data loss during chaos
- **Service availability** - Graceful degradation

## 🔧 **Fast Commands (Daily Use)**

### **Smoke Test (Local)**
```bash
# Quick local verification
python -m pytest -m "phase6_perf or phase8_e2e" -q
python scripts/aggregate_reports.py && python scripts/check_perf_budget.py
```

### **Triage Commands**
```bash
# E2E quick summary
python scripts/summarize_e2e.py

# Performance check
python scripts/check_perf_budget.py

# Flake report
python scripts/flake_detector.py report

# Status badge
python scripts/status_badge.py markdown
```

### **Budget & Sample Configuration**
```bash
# PR configuration (lenient)
export SLO_VERIFY_P95_MS=15 SLO_ENCODE_P95_MS=150 SLO_GQL_P95_MS=150
export GQL_SAMPLES=20 GQL_WARMUP=3 ENC_MB=1

# Main/Nightly configuration (strict)
export SLO_VERIFY_P95_MS=8 SLO_ENCODE_P95_MS=80 SLO_GQL_P95_MS=80
export GQL_SAMPLES=100 GQL_WARMUP=10 ENC_MB=4
```

## 🛡️ **Guardrails to Keep**

### **Status Badge Management**
- **Source under version control** - Never edit manually
- **Update only from CI** - After tests run successfully
- **Version control** - Badge changes tracked in git
- **CI integration** - Automatic updates in workflow

### **Secrets Hygiene**
- **Never log raw headers/tokens** - Use secrets redactor utilities
- **Pre-commit hooks** - Prevent secrets in commits
- **CI validation** - Verify redaction in logs
- **Regular audits** - Check for new sensitive patterns

### **Test Tagging**
- **Large tests**: Tag with `no_ci` for PRs
- **Chaos tests**: Tag with `no_ci` for PRs
- **Performance tests**: Tag with `phase6_perf`
- **E2E tests**: Tag with `phase8_e2e`
- **Chaos tests**: Tag with `phase9_chaos`

## 📈 **Performance Monitoring**

### **Key Metrics to Track**
- **Performance budgets** - p95 latencies
- **E2E success rate** - Publish/install/use success
- **Flake rate** - Test reliability
- **Chaos recovery** - Resilience metrics
- **Artifact health** - Upload success rates

### **Alerting Thresholds**
- **Performance regression** - >10% increase in p95
- **E2E failure rate** - >5% failure rate
- **Flake rate** - >2% flake rate
- **Chaos failure** - <95% success rate
- **Artifact failure** - Any upload failure

## 🎯 **Success Metrics**

### **Daily Targets**
- **CI success rate** - >95%
- **Performance stability** - No regressions >5%
- **E2E success rate** - >98%
- **Flake rate** - <1%
- **Chaos success rate** - >95%

### **Weekly Targets**
- **Baseline stability** - No updates needed
- **Quarantine health** - <5% of tests quarantined
- **Performance trends** - Stable or improving
- **Chaos coverage** - All scenarios tested

### **Monthly Targets**
- **New chaos scenarios** - 1 new scenario added
- **Performance optimization** - 5% improvement
- **Flake reduction** - 10% reduction in flaky tests
- **Operational efficiency** - Faster triage times

## 🚀 **Steady State Success**

**Your Hologram pipeline is now in steady state with:**
- ✅ **Automated operations** - Nightly runs and monitoring
- ✅ **Efficient triage** - Fast diagnosis and resolution
- ✅ **Proactive management** - Quarantine and baseline hygiene
- ✅ **Continuous improvement** - Monthly chaos enhancements
- ✅ **Operational excellence** - Clear metrics and targets

**Next**: Consider optional enhancements (Slack notifier, flamegraphs, multi-peer IPFS).

---

*Generated on: $(date)*
*Status: STEADY STATE OPERATIONS* ✅

# 🔥 Go-Live Checklist - Hologram Pipeline

**Status**: ✅ **READY FOR PRODUCTION** - Complete go-live checklist for enterprise deployment

## 🚀 One-Time Setup (Go-Live)

### ✅ **Secrets Configuration**
- [ ] Set `GRAPHQL_URL` in GitHub Actions secrets
- [ ] Set `IPFS_API` in GitHub Actions secrets  
- [ ] Set `E2E_APP_NAME` in GitHub Actions secrets
- [ ] Verify secrets redaction in CI logs (no raw tokens/headers)
- [ ] Test secrets access in CI environment

### ✅ **Performance Budgets**
- [ ] Branch-aware SLOs exported in workflow:
  - **PR**: `SLO_VERIFY_P95_MS=15`, `SLO_ENCODE_P95_MS=150`, `SLO_GQL_P95_MS=150`
  - **Main**: `SLO_VERIFY_P95_MS=8`, `SLO_ENCODE_P95_MS=80`, `SLO_GQL_P95_MS=80`
- [ ] Sample sizes configured:
  - **PR**: `GQL_SAMPLES=20`, `GQL_WARMUP=3`, `ENC_MB=1`
  - **Main/Nightly**: `GQL_SAMPLES=100`, `GQL_WARMUP=10`, `ENC_MB=4`
- [ ] Regression threshold set: `REGRESSION_THRESHOLD_PCT=10`

### ✅ **Performance Gating**
- [ ] Hard-fail enabled (removed `|| true` from CI)
- [ ] Baseline comparison wired and working
- [ ] Thresholds documented in CI workflow
- [ ] Budget violations fail CI with clear error messages

### ✅ **Artifacts & Reporting**
- [ ] `reports/index.html` uploaded to GitHub Actions
- [ ] Performance CSVs uploaded with 7-14 day retention
- [ ] `reports/e2e/events.jsonl` uploaded
- [ ] `reports/perf/baseline.json` uploaded
- [ ] Artifact retention policy configured

### ✅ **Status Badge**
- [ ] `scripts/status_badge.py` output added to README
- [ ] Badge updated in CI after tests run
- [ ] Badge source under version control
- [ ] Visual pipeline health indicator working

### ✅ **Flake Quarantine**
- [ ] Flake detector's skip list loaded by `pytest.ini`
- [ ] Quarantined tests marked with `-m "not quarantined"`
- [ ] Flake database (`reports/flake_database.json`) created
- [ ] Quarantine policy: ≥2 flakes in 7 days

### ✅ **Chaos Testing Scope**
- [ ] Phase 9 tests marked `no_ci` for PRs
- [ ] Scheduled nightly run enabled for chaos tests
- [ ] Chaos tests skip gracefully if services unavailable
- [ ] Chaos test results integrated with reporting

### ✅ **Pre-commit Hooks**
- [ ] Pre-commit hooks installed: `pre-commit install`
- [ ] Secrets detection working
- [ ] Flake detection working
- [ ] Proof chain validation working

### ✅ **SBOM/Provenance (Optional)**
- [ ] **Decision**: When to add CycloneDX + Cosign gate
- [ ] **Timeline**: 60-day roadmap item
- [ ] **Scope**: Supply chain security for `core/` artifacts

## 🔧 **Configuration Verification**

### **CI Workflow Check**
```yaml
# Verify these are set in .github/workflows/reports.yml
env:
  SLO_VERIFY_P95_MS: ${{ matrix.type == 'main' && '8' || '10' }}
  SLO_ENCODE_P95_MS: ${{ matrix.type == 'main' && '80' || '100' }}
  SLO_GQL_P95_MS: ${{ matrix.type == 'main' && '80' || '100' }}
  GQL_SAMPLES: ${{ matrix.type == 'pr' && '20' || '100' }}
  GQL_WARMUP: ${{ matrix.type == 'pr' && '3' || '10' }}
  ENC_MB: ${{ matrix.type == 'pr' && '1' || '4' }}
```

### **Secrets Check**
```bash
# Verify these are set in GitHub Actions secrets
GRAPHQL_URL=https://your-graphql-endpoint.com/graphql
IPFS_API=https://your-ipfs-endpoint.com
E2E_APP_NAME=demo/app/hello
```

### **Artifacts Check**
```yaml
# Verify artifact upload in CI
- name: Upload reports
  uses: actions/upload-artifact@v4
  with:
    name: hologram-reports-${{ matrix.type }}
    path: reports
    retention-days: 14
```

## 🚨 **Pre-Go-Live Testing**

### **Local Smoke Test**
```bash
# Run complete smoke test
export IPFS_API=http://127.0.0.1:5001
export GRAPHQL_URL=http://localhost:4000/graphql
python -m pytest -m "phase6_perf or phase8_e2e" -q
python scripts/aggregate_reports.py
python scripts/check_perf_budget.py
```

### **CI Integration Test**
```bash
# Test CI workflow locally
act -j reports --secret-file .secrets
```

### **Secrets Redaction Test**
```bash
# Test secrets redaction
python scripts/secrets_redactor.py --pre-commit test_file.py
```

### **Flake Detection Test**
```bash
# Test flake detection
python scripts/flake_detector.py detect
python scripts/flake_detector.py report
```

## 📊 **Success Criteria**

### **Go-Live Ready When:**
- [ ] All secrets configured and accessible
- [ ] Performance budgets enforced in CI
- [ ] Artifacts uploading successfully
- [ ] Status badge showing correct status
- [ ] Flake quarantine working
- [ ] Chaos tests running nightly
- [ ] Pre-commit hooks preventing secrets
- [ ] Local smoke test passes
- [ ] CI integration test passes

### **Performance Targets**
- [ ] PR runs complete in <10 minutes
- [ ] Main runs complete in <20 minutes
- [ ] Nightly runs complete in <30 minutes
- [ ] Artifact upload <2 minutes
- [ ] Report generation <1 minute

## 🎯 **Go-Live Day**

### **Morning (Pre-Deploy)**
1. **Final verification** of all checklist items
2. **Secrets validation** in CI environment
3. **Performance baseline** establishment
4. **Team notification** of go-live

### **Deploy**
1. **Merge go-live PR** with all configurations
2. **Monitor first CI run** for any issues
3. **Verify artifacts** are uploading
4. **Check status badge** updates

### **Post-Deploy (First Hour)**
1. **Monitor CI runs** for stability
2. **Verify performance budgets** are enforced
3. **Check flake detection** is working
4. **Confirm chaos tests** are scheduled

### **Post-Deploy (First Day)**
1. **Review first reports** in `reports/index.html`
2. **Verify E2E events** in `events.jsonl`
3. **Check performance baselines** are established
4. **Confirm quarantine system** is active

## 🚀 **Go-Live Success**

**Your Hologram pipeline is now LIVE with:**
- ✅ **Enterprise-grade CI/CD** with performance gating
- ✅ **Comprehensive reporting** and audit trails
- ✅ **Flake prevention** and automatic quarantine
- ✅ **Security hardening** with secrets hygiene
- ✅ **Chaos testing** for resilience validation
- ✅ **Operational excellence** with clear runbooks

**Next**: Move to Day-2 Operations for steady-state management.

---

*Generated on: $(date)*
*Status: READY FOR GO-LIVE* ✅

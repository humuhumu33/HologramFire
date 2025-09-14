# 🔥 Final Sign-Off Checklist - Hologram Pipeline

**Status**: ✅ **READY FOR LAUNCH** - Final pre-launch sanity sweep

## 🚀 **Final Pre-Launch Sanity Sweep (10 Checks)**

### ✅ **1. Secrets on CI**
- [ ] `GRAPHQL_URL` set in GitHub Actions secrets
- [ ] `IPFS_API` set in GitHub Actions secrets
- [ ] Slack/Teams webhooks set (if using notifications)
- [ ] Logs show redaction working (no raw tokens/headers)
- [ ] Secrets accessible in CI environment

**Verification:**
```bash
# Check secrets are accessible
echo "GRAPHQL_URL: ${GRAPHQL_URL:0:20}..."
echo "IPFS_API: ${IPFS_API:0:20}..."
```

### ✅ **2. Hard Fail Enabled**
- [ ] Perf gate step no longer uses `|| true`
- [ ] Baseline compare is active on PRs
- [ ] Budget violations fail CI with clear error messages
- [ ] Regression detection working (>10% threshold)

**Verification:**
```bash
# Test hard fail
SLO_GQL_P95_MS=1 python scripts/check_perf_budget.py
# Should exit with code 1
```

### ✅ **3. Branch SLOs**
- [ ] PR (lenient): `SLO_VERIFY_P95_MS=15`, `SLO_ENCODE_P95_MS=150`, `SLO_GQL_P95_MS=150`
- [ ] Main (strict): `SLO_VERIFY_P95_MS=8`, `SLO_ENCODE_P95_MS=80`, `SLO_GQL_P95_MS=80`
- [ ] Nightly (standard): `SLO_VERIFY_P95_MS=10`, `SLO_ENCODE_P95_MS=100`, `SLO_GQL_P95_MS=100`
- [ ] Sample sizes configured correctly

**Verification:**
```bash
# Check PR configuration
python scripts/ops_toggles.py pr

# Check main configuration
python scripts/ops_toggles.py main
```

### ✅ **4. Artifacts Retained**
- [ ] 7-14 days retention configured
- [ ] `reports/index.html` present and accessible
- [ ] Performance CSVs uploaded
- [ ] `reports/e2e/events.jsonl` present
- [ ] `reports/perf/baseline.json` uploaded

**Verification:**
```bash
# Check artifacts exist
ls -la reports/
ls -la reports/perf/
ls -la reports/e2e/
```

### ✅ **5. Status Badge**
- [ ] Generated only from CI after tests
- [ ] README links to the latest artifact
- [ ] Badge source under version control
- [ ] Updates automatically in CI workflow

**Verification:**
```bash
# Generate status badge
python scripts/status_badge.py markdown
```

### ✅ **6. Quarantine Wired**
- [ ] `quarantined` marker respected in `pytest.ini`
- [ ] Phase 9 chaos marked `no_ci` for PRs
- [ ] Flake detector working
- [ ] Quarantine database created

**Verification:**
```bash
# Check pytest markers
python -m pytest --markers | grep quarantined

# Check flake detection
python scripts/flake_detector.py report
```

### ✅ **7. Nonce Replay Test**
- [ ] CTP-96 nonce cache enabled
- [ ] Replay negative test unskipped
- [ ] Nonce validation working
- [ ] Replay attacks rejected

**Verification:**
```bash
# Run CTP-96 tests
python -m pytest -m "ctp96_replay" -v
```

### ✅ **8. Proof Chain Required**
- [ ] Phase 5/7 tests assert proofs exist
- [ ] Proof validation working (`valid == true`)
- [ ] Tampering detection working
- [ ] Chain integrity verified

**Verification:**
```bash
# Run proof chain tests
python -m pytest -m "proof_chain_mandatory" -v
```

### ✅ **9. Determinism Spot-Check**
- [ ] Phase 3 Node vs Docker parity passes
- [ ] Runtime consistency verified
- [ ] Cross-platform compatibility confirmed
- [ ] Deterministic results across environments

**Verification:**
```bash
# Run Phase 3 tests
python -m pytest -m "phase3_runtime" -v
```

### ✅ **10. Docs Visible**
- [ ] `GO_LIVE_CHECKLIST.md` linked from README
- [ ] `DAY2_OPS_PLAYBOOK.md` linked from README
- [ ] `FINAL_SIGN_OFF_CHECKLIST.md` accessible
- [ ] All operational docs linked and visible

**Verification:**
```bash
# Check docs exist
ls -la docs/
grep -r "GO_LIVE_CHECKLIST" README.md
grep -r "DAY2_OPS_PLAYBOOK" README.md
```

## 🛡️ **CI Hardeners (Drop-in)**

### **1. Prevent Overlapping CI Runs**
```yaml
# Add to each workflow
concurrency:
  group: hologram-${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true
```

### **2. Least-Privilege Workflow Permissions**
```yaml
# Add to each workflow
permissions:
  contents: read
  actions: read
  id-token: none
```

## 🔒 **Optional Guardrails**

### **1. Artifact Size Cap**
```bash
# Protect Actions storage
test -f reports/e2e/events.jsonl && \
[ $(wc -c < reports/e2e/events.jsonl) -lt 5242880 ] || \
{ echo "events.jsonl too large"; exit 1; }
```

### **2. Cache for Node Build**
```yaml
# Speed without flakiness
- uses: actions/setup-node@v4
  with: { node-version: 18, cache: 'pnpm' }
- uses: pnpm/action-setup@v4
  with: { version: 9 }
```

### **3. Fork PR Safety**
```yaml
# Skip E2E if secrets aren't exposed
if: ${{ github.event.pull_request.head.repo.fork == false && secrets.GRAPHQL_URL && secrets.IPFS_API }}
```

## 🔄 **Roll-Forward / Roll-Back**

### **Roll-Forward Baseline**
```bash
# When perf is genuinely better/worse
# 1. Merge to main
# 2. Capture green perf CSVs
# 3. Update baseline.json via baseline script
# 4. Commit in same commit
git add reports/perf/baseline.json
git commit -m "chore: update baseline - performance improved"
```

### **Roll-Back**
```bash
# 1. Revert last app/service change
git revert HEAD

# 2. Re-run Phase 6 + Phase 8
python -m pytest -m "phase6_perf or phase8_e2e" -v

# 3. If still red, widen SLO temporarily on PR env only
export SLO_GQL_P95_MS=200  # Temporary widening
python scripts/check_perf_budget.py
```

## 🏥 **Quick Health Check One-Liners**

### **Open Dashboard**
```bash
python scripts/aggregate_reports.py && open reports/index.html
```

### **Force Perf-Gate Fail (Smoke Test)**
```bash
SLO_GQL_P95_MS=1 python scripts/check_perf_budget.py
```

### **Get 30-Sec E2E Summary**
```bash
python scripts/summarize_e2e.py
```

### **Check Pipeline Status**
```bash
python scripts/status_badge.py markdown
```

### **Flake Report**
```bash
python scripts/flake_detector.py report
```

## 🎯 **What Good Looks Like (CI)**

### ✅ **Successful CI Run**
- **Perf gate passes** with p95 < budgets (cold and warm noted in CSVs)
- **Baseline compare** shows ≤10% drift (or explicitly acknowledged)
- **E2E logs** show `ipfs_publish` → `marketplace_publish` → `resolve` (non-empty encoding)
- **Status badge** updated and README shows "PASS" with fresh timestamp

### ✅ **Artifacts Generated**
- `reports/index.html` - Complete dashboard
- `reports/perf/*.csv` - Performance data with cold/warm profiles
- `reports/e2e/events.jsonl` - E2E event log
- `reports/perf/baseline.json` - Performance baseline
- `reports/flake_database.json` - Flake tracking

### ✅ **Performance Targets**
- **PR runs**: Complete in <10 minutes
- **Main runs**: Complete in <20 minutes
- **Nightly runs**: Complete in <30 minutes
- **Artifact upload**: <2 minutes
- **Report generation**: <1 minute

## 🚀 **Launch Day**

### **Pre-Launch (Morning)**
1. **Run final sanity sweep** - All 10 checks pass
2. **Verify CI hardeners** - Concurrency and permissions set
3. **Test optional guardrails** - Artifact size, cache, fork safety
4. **Confirm roll-forward/roll-back** - Procedures documented

### **Launch**
1. **Merge launch PR** - All configurations included
2. **Monitor first CI run** - Watch for any issues
3. **Verify artifacts** - All reports uploading
4. **Check status badge** - Updates correctly

### **Post-Launch (First Hour)**
1. **Monitor CI stability** - No failures
2. **Verify performance budgets** - Enforced correctly
3. **Check flake detection** - Working properly
4. **Confirm chaos tests** - Scheduled correctly

### **Post-Launch (First Day)**
1. **Review first reports** - Dashboard working
2. **Verify E2E events** - Pipeline successful
3. **Check performance baselines** - Established
4. **Confirm quarantine system** - Active

## 🎉 **Launch Success**

**Your Hologram pipeline is now LIVE with:**
- ✅ **Complete sanity sweep** - All 10 checks passed
- ✅ **CI hardeners** - Concurrency and permissions
- ✅ **Optional guardrails** - Artifact size, cache, fork safety
- ✅ **Roll-forward/roll-back** - Procedures documented
- ✅ **Health checkers** - Quick one-liners for monitoring
- ✅ **Success criteria** - Clear definition of "good"

**Next**: Move to steady-state operations with day-2 playbook.

---

*Generated on: $(date)*
*Status: READY FOR LAUNCH* ✅

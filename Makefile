.PHONY: phase0 phase1 phase2 phase3 phase4 phase5 phase6 phase6-fast perf-report phase7 phase8 all-phases help docker-pull reports perf-gate

# Phase 0 - Repo Readiness & Wiring (NO MOCKS, PROD ONLY)
phase0:
	pytest -m phase0_ready

# Phase 1 - Core math & invariants
phase1:
	pytest -m phase1_core

# Phase 2 - BHIC/CEF/UORID pipeline
phase2:
	pytest -m phase2_integration

# Phase 3 - Parity across runtimes
docker-pull:
	docker pull node:18-alpine

phase3: docker-pull
	pytest -m phase3_runtime -v

# Phase 4 - IPFS/CTP-96
phase4:
	pytest -m phase4_network

# Phase 5 - Named content + proof chain
phase5:
	pytest -m phase5_graphql

# Phase 6 - Performance SLOs (encode/verify + GraphQL)
phase6:
	pytest -m phase6_perf -v

phase6-fast:
	SLO_ENCODE_P95_MS=250 SLO_VERIFY_P95_MS=20 SLO_GQL_P95_MS=200 \
	ENC_MB=1 GQL_SAMPLES=20 GQL_WARMUP=3 \
	pytest -m phase6_perf -q

perf-report:
	@echo "Perf CSVs written to reports/perf/"
	@ls -1 reports/perf || true

# Phase 7 - Security/Abuse (tamper • replay • malformed)
phase7:
	pytest -m phase7_security -v

# Phase 8 - Publisher→Marketplace→Install→Use
phase8:
	pytest -m phase8_e2e

# Run all phases
all-phases: phase0 phase1 phase2 phase3 phase4 phase5 phase6 phase7 phase8

# Reports & Gating
reports:
	python scripts/aggregate_reports.py
	@echo "Open reports/index.html"

perf-gate:
	python scripts/check_perf_budget.py

# Help target
help:
	@echo "Available targets:"
	@echo "  phase0    - Repo readiness & wiring (prod only)"
	@echo "  phase1    - Core math & invariants"
	@echo "  phase2    - BHIC/CEF/UORID pipeline"
	@echo "  phase3    - Runtime parity (Node/Docker/optional WASM/EFI/U-Boot)"
	@echo "  docker-pull - Pull node:18-alpine Docker image"
	@echo "  phase4    - IPFS/CTP-96"
	@echo "  phase5    - Named content + proof chain"
	@echo "  phase6    - Performance SLOs (encode/verify + GraphQL)"
	@echo "  phase6-fast - Quick perf test with relaxed thresholds"
	@echo "  perf-report - Show performance CSV artifacts"
	@echo "  phase7    - Tamper/replay"
	@echo "  phase8    - Publisher→Marketplace→Install→Use"
	@echo "  reports   - Generate HTML report from perf + E2E data"
	@echo "  perf-gate - Check performance budgets (exit 1 if exceeded)"
	@echo "  all-phases - Run all phases"
	@echo "  help      - Show this help"
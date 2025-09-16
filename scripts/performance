import csv, os, sys
from pathlib import Path

PERF_DIR = Path("reports/perf")

# env overrides (defaults match your Phase 6 pack)
BUDGETS = {
  "core.verify_ms": float(os.getenv("SLO_VERIFY_P95_MS", "10")),
  "core.encode_1MB_ms": float(os.getenv("SLO_ENCODE_P95_MS", "100")),
  "graphql.resolve_ms": float(os.getenv("SLO_GQL_P95_MS", "100")),
}

def rows():
    for p in PERF_DIR.glob("*.csv"):
        with p.open(newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                yield row

def key(row):
    return f"{row['suite']}.{row['metric']}"

def main():
    have = {}
    for row in rows():
        k = key(row)
        try:
            p95 = float(row["p95_ms"])
        except:
            continue
        if k not in have or p95 < have[k]:
            have[k] = p95

    violations = []
    for k, budget in BUDGETS.items():
        if k in have and have[k] > budget:
            violations.append((k, have[k], budget))

    if violations:
        print("❌ Perf budget violations:")
        for k, val, budget in violations:
            print(f"  {k}: p95={val:.2f}ms > budget={budget:.2f}ms")
        sys.exit(1)

    print("✅ Perf budgets OK")
    sys.exit(0)

if __name__ == "__main__":
    main()

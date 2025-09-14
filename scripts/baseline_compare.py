#!/usr/bin/env python3
"""
Compare current performance against baseline from main branch.
Fails if performance regresses beyond threshold even if still under SLO.
"""
import csv, json, os, sys
from pathlib import Path
from collections import defaultdict

PERF_DIR = Path("reports/perf")
BASELINE_FILE = Path("reports/perf/baseline.json")
REGRESSION_THRESHOLD = float(os.getenv("REGRESSION_THRESHOLD_PCT", "10"))  # 10% regression threshold

def read_current_perf():
    """Read current performance data."""
    current = {}
    for p in PERF_DIR.glob("*.csv"):
        with p.open(newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                key = f"{row['suite']}.{row['metric']}"
                try:
                    p95 = float(row["p95_ms"])
                    current[key] = p95
                except:
                    continue
    return current

def read_baseline():
    """Read baseline performance data."""
    if not BASELINE_FILE.exists():
        return {}
    
    try:
        with BASELINE_FILE.open("r", encoding="utf-8") as f:
            return json.load(f)
    except:
        return {}

def save_baseline(perf_data):
    """Save current performance as baseline."""
    BASELINE_FILE.parent.mkdir(parents=True, exist_ok=True)
    with BASELINE_FILE.open("w", encoding="utf-8") as f:
        json.dump(perf_data, f, indent=2)
    print(f"💾 Saved baseline to {BASELINE_FILE}")

def main():
    current = read_current_perf()
    baseline = read_baseline()
    
    # If no baseline exists, save current as baseline
    if not baseline:
        if current:
            save_baseline(current)
            print("✅ No baseline found, saved current performance as baseline")
        else:
            print("⚠️  No performance data found")
        return
    
    # Compare against baseline
    regressions = []
    improvements = []
    
    for metric, current_p95 in current.items():
        if metric not in baseline:
            print(f"ℹ️  New metric: {metric} (no baseline)")
            continue
        
        baseline_p95 = baseline[metric]
        pct_change = ((current_p95 - baseline_p95) / baseline_p95) * 100
        
        if pct_change > REGRESSION_THRESHOLD:
            regressions.append((metric, baseline_p95, current_p95, pct_change))
        elif pct_change < -5:  # 5% improvement threshold
            improvements.append((metric, baseline_p95, current_p95, pct_change))
    
    # Report results
    if regressions:
        print("❌ Performance regressions detected:")
        for metric, baseline_p95, current_p95, pct_change in regressions:
            print(f"  {metric}: {baseline_p95:.1f}ms → {current_p95:.1f}ms (+{pct_change:.1f}%)")
        sys.exit(1)
    
    if improvements:
        print("✅ Performance improvements:")
        for metric, baseline_p95, current_p95, pct_change in improvements:
            print(f"  {metric}: {baseline_p95:.1f}ms → {current_p95:.1f}ms ({pct_change:.1f}%)")
    
    if not regressions and not improvements:
        print("✅ Performance stable (no significant changes)")
    
    # Update baseline if this is main branch
    if os.getenv("GITHUB_REF") == "refs/heads/main":
        save_baseline(current)

if __name__ == "__main__":
    main()

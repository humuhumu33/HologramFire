#!/usr/bin/env python3
"""
Generate CI job summary with performance metrics and E2E highlights.
Writes to $GITHUB_STEP_SUMMARY for GitHub Actions integration.
"""
import csv, json, os, sys
from pathlib import Path
from collections import defaultdict

PERF_DIR = Path("reports/perf")
E2E_DIR = Path("reports/e2e")
SUMMARY_FILE = os.getenv("GITHUB_STEP_SUMMARY", "/dev/stdout")

def read_perf_best():
    """Get best p95 per metric from all perf CSVs."""
    best = {}
    for p in PERF_DIR.glob("*.csv"):
        with p.open(newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                key = f"{row['suite']}.{row['metric']}"
                try:
                    p95 = float(row["p95_ms"])
                except:
                    continue
                if key not in best or p95 < best[key]:
                    best[key] = p95
    return best

def read_e2e_highlights():
    """Get latest E2E events for summary."""
    events = []
    f = E2E_DIR / "events.jsonl"
    if f.exists():
        for line in f.read_text(encoding="utf-8").splitlines():
            try:
                events.append(json.loads(line))
            except:
                pass
    
    # Group by event type, get latest
    latest = {}
    for ev in events:
        event_type = ev.get("event", "unknown")
        if event_type not in latest or ev.get("ts", "") > latest[event_type].get("ts", ""):
            latest[event_type] = ev
    
    return latest

def main():
    perf_best = read_perf_best()
    e2e_highlights = read_e2e_highlights()
    
    # Generate markdown summary
    summary = ["## 🔥 Hologram Pipeline Results\n"]
    
    # Performance section
    if perf_best:
        summary.append("### 📊 Performance (Best p95)")
        summary.append("| Metric | p95 (ms) |")
        summary.append("|--------|----------|")
        for metric, p95 in sorted(perf_best.items()):
            summary.append(f"| `{metric}` | {p95:.1f} |")
        summary.append("")
    else:
        summary.append("### 📊 Performance\n*No performance data found*\n")
    
    # E2E section
    if e2e_highlights:
        summary.append("### 🚀 E2E Highlights")
        for event_type, event in sorted(e2e_highlights.items()):
            cid = event.get("cid", "N/A")[:12] + "..." if event.get("cid") else "N/A"
            name = event.get("name", "N/A")
            variant = event.get("variant", "N/A")
            ts = event.get("ts", "N/A")
            summary.append(f"- **{event_type}**: `{name}` ({variant}) - CID: `{cid}` - {ts}")
        summary.append("")
    else:
        summary.append("### 🚀 E2E\n*No E2E events found*\n")
    
    # Artifacts section
    summary.append("### 📁 Artifacts")
    summary.append("- [📊 HTML Report](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})")
    summary.append("- [📈 Performance CSVs](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})")
    summary.append("- [🎯 E2E Events](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})")
    
    # Write to summary file
    with open(SUMMARY_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(summary))
    
    print("✅ CI summary generated")

if __name__ == "__main__":
    main()

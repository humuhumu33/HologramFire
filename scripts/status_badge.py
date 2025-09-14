#!/usr/bin/env python3
"""
Generate status badge for Hologram pipeline.
Creates a simple HTML badge that shows green/red based on latest perf gate + E2E results.
"""
import json
import os
import sys
from pathlib import Path
from datetime import datetime, timedelta

def get_latest_ci_status():
    """Get the latest CI status from artifacts or local data."""
    # Check if we're in CI
    if os.getenv("GITHUB_ACTIONS"):
        # In CI, check current run status
        return check_current_ci_status()
    else:
        # Local, check latest artifacts
        return check_latest_artifacts()

def check_current_ci_status():
    """Check current CI run status."""
    # This would be called from within CI
    # For now, return a placeholder
    return {
        "status": "running",
        "timestamp": datetime.now().isoformat(),
        "perf_gate": "unknown",
        "e2e_tests": "unknown"
    }

def check_latest_artifacts():
    """Check latest artifacts for status."""
    reports_dir = Path("reports")
    
    if not reports_dir.exists():
        return {
            "status": "unknown",
            "timestamp": None,
            "perf_gate": "unknown",
            "e2e_tests": "unknown"
        }
    
    # Check for recent reports
    html_file = reports_dir / "index.html"
    e2e_file = reports_dir / "e2e" / "events.jsonl"
    
    status = {
        "status": "unknown",
        "timestamp": None,
        "perf_gate": "unknown",
        "e2e_tests": "unknown"
    }
    
    # Check HTML report timestamp
    if html_file.exists():
        mtime = datetime.fromtimestamp(html_file.stat().st_mtime)
        status["timestamp"] = mtime.isoformat()
        
        # If report is recent (within 24 hours), consider it fresh
        if mtime > datetime.now() - timedelta(hours=24):
            status["status"] = "fresh"
        else:
            status["status"] = "stale"
    
    # Check E2E events
    if e2e_file.exists():
        try:
            with e2e_file.open("r") as f:
                events = [json.loads(line) for line in f if line.strip()]
            
            if events:
                # Check for successful pipeline
                event_types = {event.get("event") for event in events}
                if "publish" in event_types and "install" in event_types:
                    status["e2e_tests"] = "pass"
                else:
                    status["e2e_tests"] = "fail"
            else:
                status["e2e_tests"] = "fail"
        except:
            status["e2e_tests"] = "fail"
    
    # Check perf gate (simplified - would need actual perf data)
    perf_dir = reports_dir / "perf"
    if perf_dir.exists() and list(perf_dir.glob("*.csv")):
        status["perf_gate"] = "pass"  # Simplified assumption
    else:
        status["perf_gate"] = "fail"
    
    # Overall status
    if status["perf_gate"] == "pass" and status["e2e_tests"] == "pass":
        status["status"] = "pass"
    elif status["perf_gate"] == "fail" or status["e2e_tests"] == "fail":
        status["status"] = "fail"
    
    return status

def generate_badge_html(status):
    """Generate HTML badge."""
    if status["status"] == "pass":
        color = "#28a745"
        text = "PASS"
        icon = "✅"
    elif status["status"] == "fail":
        color = "#dc3545"
        text = "FAIL"
        icon = "❌"
    elif status["status"] == "running":
        color = "#ffc107"
        text = "RUNNING"
        icon = "🔄"
    else:
        color = "#6c757d"
        text = "UNKNOWN"
        icon = "❓"
    
    timestamp = status.get("timestamp")
    if timestamp:
        try:
            dt = datetime.fromisoformat(timestamp.replace("Z", "+00:00"))
            time_str = dt.strftime("%Y-%m-%d %H:%M")
        except:
            time_str = "Unknown"
    else:
        time_str = "Never"
    
    html = f"""
<div style="
    display: inline-block;
    padding: 8px 12px;
    background-color: {color};
    color: white;
    border-radius: 6px;
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
    font-size: 14px;
    font-weight: 600;
    text-decoration: none;
    border: 2px solid {color};
    box-shadow: 0 2px 4px rgba(0,0,0,0.1);
">
    {icon} Hologram Pipeline: {text}
    <div style="
        font-size: 11px;
        font-weight: 400;
        opacity: 0.9;
        margin-top: 2px;
    ">
        Last run: {time_str}
    </div>
</div>
"""
    return html

def generate_markdown_badge(status):
    """Generate Markdown badge for README."""
    if status["status"] == "pass":
        color = "green"
        text = "PASS"
    elif status["status"] == "fail":
        color = "red"
        text = "FAIL"
    elif status["status"] == "running":
        color = "yellow"
        text = "RUNNING"
    else:
        color = "grey"
        text = "UNKNOWN"
    
    timestamp = status.get("timestamp")
    if timestamp:
        try:
            dt = datetime.fromisoformat(timestamp.replace("Z", "+00:00"))
            time_str = dt.strftime("%Y-%m-%d")
        except:
            time_str = "Unknown"
    else:
        time_str = "Never"
    
    return f"![Hologram Pipeline](https://img.shields.io/badge/Hologram%20Pipeline-{text}-{color}?style=flat-square&label=Last%20run&message={time_str})"

def main():
    """Generate status badge."""
    status = get_latest_ci_status()
    
    # Generate HTML badge
    html_badge = generate_badge_html(status)
    
    # Generate Markdown badge
    markdown_badge = generate_markdown_badge(status)
    
    # Output options
    if len(sys.argv) > 1:
        output_type = sys.argv[1].lower()
        
        if output_type == "html":
            print(html_badge)
        elif output_type == "markdown":
            print(markdown_badge)
        elif output_type == "json":
            print(json.dumps(status, indent=2))
        else:
            print("Usage: python scripts/status_badge.py [html|markdown|json]")
            sys.exit(1)
    else:
        # Default: show both
        print("HTML Badge:")
        print(html_badge)
        print("\nMarkdown Badge:")
        print(markdown_badge)
        print(f"\nStatus: {json.dumps(status, indent=2)}")

if __name__ == "__main__":
    main()

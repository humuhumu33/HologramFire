#!/usr/bin/env python3
"""
Quick Health Check One-Liners for Hologram Pipeline
Fast commands for monitoring pipeline health.
"""
import os
import sys
import subprocess
import webbrowser
from pathlib import Path

def open_dashboard():
    """Open the dashboard."""
    print("🔥 Opening Hologram dashboard...")
    
    # Generate reports
    result = subprocess.run(
        ["python", "scripts/aggregate_reports.py"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        html_file = Path("reports/index.html")
        if html_file.exists():
            # Open in browser
            webbrowser.open(f"file://{html_file.absolute()}")
            print("✅ Dashboard opened in browser")
        else:
            print("❌ HTML report not found")
    else:
        print(f"❌ Failed to generate reports: {result.stderr}")

def force_perf_gate_fail():
    """Force a perf-gate fail to smoke test the gate itself."""
    print("🔥 Testing perf gate with forced failure...")
    
    # Set very low SLO to force failure
    os.environ["SLO_VERIFY_P95_MS"] = "1"
    os.environ["SLO_ENCODE_P95_MS"] = "1"
    os.environ["SLO_GQL_P95_MS"] = "1"
    
    result = subprocess.run(
        ["python", "scripts/check_perf_budget.py"],
        capture_output=True, text=True
    )
    
    if result.returncode == 1:
        print("✅ Perf gate correctly failed (as expected)")
        print("Output:", result.stdout)
    else:
        print("❌ Perf gate should have failed but didn't")
        print("Output:", result.stdout)

def get_e2e_summary():
    """Get 30-second E2E summary."""
    print("🔥 Getting E2E summary...")
    
    result = subprocess.run(
        ["python", "scripts/summarize_e2e.py"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        print("✅ E2E Summary:")
        print(result.stdout)
    else:
        print(f"❌ Failed to get E2E summary: {result.stderr}")

def check_pipeline_status():
    """Check pipeline status."""
    print("🔥 Checking pipeline status...")
    
    result = subprocess.run(
        ["python", "scripts/status_badge.py", "markdown"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        print("✅ Pipeline Status:")
        print(result.stdout)
    else:
        print(f"❌ Failed to get status: {result.stderr}")

def get_flake_report():
    """Get flake report."""
    print("🔥 Getting flake report...")
    
    result = subprocess.run(
        ["python", "scripts/flake_detector.py", "report"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        print("✅ Flake Report:")
        print(result.stdout)
    else:
        print(f"❌ Failed to get flake report: {result.stderr}")

def check_performance():
    """Check performance budgets."""
    print("🔥 Checking performance budgets...")
    
    result = subprocess.run(
        ["python", "scripts/check_perf_budget.py"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        print("✅ Performance budgets OK")
        print(result.stdout)
    else:
        print("❌ Performance budget violations:")
        print(result.stdout)

def check_baseline():
    """Check baseline comparison."""
    print("🔥 Checking baseline comparison...")
    
    result = subprocess.run(
        ["python", "scripts/baseline_compare.py"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        print("✅ Baseline comparison OK")
        print(result.stdout)
    else:
        print("❌ Baseline comparison issues:")
        print(result.stdout)

def run_smoke_test():
    """Run complete smoke test."""
    print("🔥 Running complete smoke test...")
    
    # Set environment variables
    os.environ["IPFS_API"] = "http://127.0.0.1:5001"
    os.environ["GRAPHQL_URL"] = "http://localhost:4000/graphql"
    
    # Run tests
    result = subprocess.run(
        ["python", "-m", "pytest", "-m", "phase6_perf or phase8_e2e", "-q"],
        capture_output=True, text=True
    )
    
    if result.returncode == 0:
        print("✅ Smoke test passed")
    else:
        print("❌ Smoke test failed:")
        print(result.stdout)
        print(result.stderr)
    
    # Generate reports
    subprocess.run(["python", "scripts/aggregate_reports.py"])
    subprocess.run(["python", "scripts/check_perf_budget.py"])

def show_ops_toggles():
    """Show ops toggles for different environments."""
    print("🔥 Available ops toggles:")
    
    for env in ["pr", "main", "nightly", "dev"]:
        print(f"\n--- {env.upper()} Configuration ---")
        result = subprocess.run(
            ["python", "scripts/ops_toggles.py", env],
            capture_output=True, text=True
        )
        if result.returncode == 0:
            print(result.stdout)
        else:
            print(f"❌ Failed to get {env} configuration")

def main():
    """Main function."""
    if len(sys.argv) < 2:
        print("🔥 Hologram Pipeline Health Check")
        print("=" * 40)
        print("Available commands:")
        print("  dashboard     - Open dashboard in browser")
        print("  perf-fail     - Force perf gate fail (smoke test)")
        print("  e2e-summary   - Get 30-second E2E summary")
        print("  status        - Check pipeline status")
        print("  flake-report  - Get flake report")
        print("  performance   - Check performance budgets")
        print("  baseline      - Check baseline comparison")
        print("  smoke-test    - Run complete smoke test")
        print("  ops-toggles   - Show ops toggles")
        print("  all           - Run all health checks")
        return
    
    command = sys.argv[1].lower()
    
    if command == "dashboard":
        open_dashboard()
    elif command == "perf-fail":
        force_perf_gate_fail()
    elif command == "e2e-summary":
        get_e2e_summary()
    elif command == "status":
        check_pipeline_status()
    elif command == "flake-report":
        get_flake_report()
    elif command == "performance":
        check_performance()
    elif command == "baseline":
        check_baseline()
    elif command == "smoke-test":
        run_smoke_test()
    elif command == "ops-toggles":
        show_ops_toggles()
    elif command == "all":
        print("🔥 Running all health checks...")
        check_pipeline_status()
        check_performance()
        check_baseline()
        get_e2e_summary()
        get_flake_report()
        print("\n✅ All health checks completed")
    else:
        print(f"❌ Unknown command: {command}")
        sys.exit(1)

if __name__ == "__main__":
    main()

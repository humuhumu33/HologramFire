#!/usr/bin/env python3
"""
E2E Test Suite Runner for Hologram Fire

This script runs the complete E2E test suite including:
- Basic E2E tests (publish, register, resolve, verify)
- Strict E2E tests (no fallbacks)
- Performance E2E tests (with load generation)
- Stress tests

Usage:
    python tests/phase8_e2e/run_e2e_suite.py [options]

Environment Variables:
    IPFS_API         - IPFS API endpoint (required)
    GRAPHQL_URL      - GraphQL endpoint (required)
    GRAPHQL_TOKEN    - Optional authentication token
    E2E_PERF_*       - Performance test parameters
    E2E_STRESS_*     - Stress test parameters
"""

import os
import sys
import json
import time
import argparse
import subprocess
from pathlib import Path

def run_command(cmd, description):
    """Run a command and return the result"""
    print(f"\n{'='*60}")
    print(f"🚀 {description}")
    print(f"{'='*60}")
    print(f"Command: {' '.join(cmd)}")
    print()
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=300  # 5 minute timeout
        )
        duration = time.time() - start_time
        
        print(f"Exit code: {result.returncode}")
        print(f"Duration: {duration:.2f}s")
        
        if result.stdout:
            print("STDOUT:")
            print(result.stdout)
        
        if result.stderr:
            print("STDERR:")
            print(result.stderr)
        
        return result.returncode == 0, result.stdout, result.stderr
        
    except subprocess.TimeoutExpired:
        print("❌ Command timed out after 5 minutes")
        return False, "", "Timeout"
    except Exception as e:
        print(f"❌ Command failed: {e}")
        return False, "", str(e)

def check_environment():
    """Check required environment variables"""
    required_vars = ["IPFS_API", "GRAPHQL_URL"]
    missing = []
    
    for var in required_vars:
        if not os.getenv(var):
            missing.append(var)
    
    if missing:
        print(f"❌ Missing required environment variables: {', '.join(missing)}")
        print("\nPlease set:")
        for var in missing:
            print(f"  export {var}=<your-value>")
        return False
    
    print("✅ Environment variables check passed")
    return True

def run_test_suite(test_type, verbose=False):
    """Run a specific test suite"""
    
    # Base pytest command
    cmd = ["python", "-m", "pytest", "-v" if verbose else "-q"]
    
    # Test file patterns
    test_files = {
        "basic": "tests/phase8_e2e/test_e2e_publish_install.py",
        "strict": "tests/phase8_e2e/test_e2e_strict.py",
        "performance": "tests/phase8_e2e/test_e2e_load_integration.py::test_e2e_with_load_generation",
        "stress": "tests/phase8_e2e/test_e2e_load_integration.py::test_e2e_stress_test",
        "all": "tests/phase8_e2e/"
    }
    
    if test_type not in test_files:
        print(f"❌ Unknown test type: {test_type}")
        return False
    
    # Add test file
    cmd.append(test_files[test_type])
    
    # Add markers
    if test_type == "performance":
        cmd.extend(["-m", "performance"])
    elif test_type == "stress":
        cmd.extend(["-m", "performance"])
    elif test_type == "strict":
        cmd.extend(["-m", "strict"])
    elif test_type == "basic":
        cmd.extend(["-m", "phase8_e2e"])
    
    # Run the test
    success, stdout, stderr = run_command(cmd, f"Running {test_type} E2E tests")
    
    if success:
        print(f"✅ {test_type.title()} tests passed")
    else:
        print(f"❌ {test_type.title()} tests failed")
    
    return success

def generate_report():
    """Generate a test report from the events"""
    events_dir = Path("reports/e2e")
    if not events_dir.exists():
        print("No events directory found")
        return
    
    report = {
        "timestamp": time.time(),
        "tests": {},
        "summary": {
            "total_tests": 0,
            "passed": 0,
            "failed": 0
        }
    }
    
    # Collect events from all JSONL files
    for event_file in events_dir.glob("*.jsonl"):
        test_suite = event_file.stem
        events = []
        
        try:
            with open(event_file, 'r') as f:
                for line in f:
                    if line.strip():
                        events.append(json.loads(line))
            
            report["tests"][test_suite] = {
                "event_count": len(events),
                "events": events
            }
            
        except Exception as e:
            print(f"Warning: Could not read {event_file}: {e}")
    
    # Write report
    report_file = Path("reports/e2e_test_report.json")
    report_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(report_file, 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"📊 Test report generated: {report_file}")

def main():
    parser = argparse.ArgumentParser(description="Run Hologram Fire E2E test suite")
    parser.add_argument("--test", choices=["basic", "strict", "performance", "stress", "all"], 
                       default="all", help="Which tests to run")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--skip-env-check", action="store_true", help="Skip environment check")
    parser.add_argument("--report", action="store_true", help="Generate test report")
    
    args = parser.parse_args()
    
    print("🔥 Hologram Fire E2E Test Suite")
    print("=" * 50)
    
    # Check environment
    if not args.skip_env_check:
        if not check_environment():
            sys.exit(1)
    
    # Show current environment
    print("\n📋 Current Environment:")
    print(f"  IPFS_API: {os.getenv('IPFS_API', 'Not set')}")
    print(f"  GRAPHQL_URL: {os.getenv('GRAPHQL_URL', 'Not set')}")
    print(f"  GRAPHQL_TOKEN: {'Set' if os.getenv('GRAPHQL_TOKEN') else 'Not set'}")
    
    # Performance test parameters
    print(f"  E2E_LOAD_DURATION: {os.getenv('E2E_LOAD_DURATION', '5')}s")
    print(f"  E2E_LOAD_WORKERS: {os.getenv('E2E_LOAD_WORKERS', '4')}")
    print(f"  E2E_LOAD_PAYLOAD: {os.getenv('E2E_LOAD_PAYLOAD', '1024')}B")
    print(f"  E2E_LOAD_OPS_PER_SEC: {os.getenv('E2E_LOAD_OPS_PER_SEC', '10')}")
    
    # Run tests
    start_time = time.time()
    
    if args.test == "all":
        test_types = ["basic", "strict", "performance", "stress"]
    else:
        test_types = [args.test]
    
    results = {}
    for test_type in test_types:
        results[test_type] = run_test_suite(test_type, args.verbose)
    
    total_duration = time.time() - start_time
    
    # Summary
    print(f"\n{'='*60}")
    print("📊 TEST SUMMARY")
    print(f"{'='*60}")
    
    passed = sum(1 for success in results.values() if success)
    total = len(results)
    
    for test_type, success in results.items():
        status = "✅ PASSED" if success else "❌ FAILED"
        print(f"  {test_type.title():12} {status}")
    
    print(f"\nTotal: {passed}/{total} test suites passed")
    print(f"Duration: {total_duration:.2f}s")
    
    # Generate report if requested
    if args.report:
        generate_report()
    
    # Exit with appropriate code
    if passed == total:
        print("\n🎉 All tests passed!")
        sys.exit(0)
    else:
        print(f"\n💥 {total - passed} test suite(s) failed")
        sys.exit(1)

if __name__ == "__main__":
    main()

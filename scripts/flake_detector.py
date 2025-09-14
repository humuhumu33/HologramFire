#!/usr/bin/env python3
"""
Flake Detection and Quarantine System
Detects flaky tests and automatically quarantines them.
"""
import json
import os
import sys
from pathlib import Path
from typing import Dict, Any, List, Set
from collections import defaultdict, Counter
import subprocess

FLAKE_DB_FILE = Path("reports/flake_database.json")
QUARANTINE_FILE = Path("reports/quarantined_tests.json")
FLAKE_THRESHOLD = 2  # Tests that flake twice get quarantined

class FlakeDetector:
    """Detects and manages flaky tests."""
    
    def __init__(self):
        self.flake_db = self._load_flake_db()
        self.quarantined_tests = self._load_quarantined_tests()
    
    def _load_flake_db(self) -> Dict[str, Any]:
        """Load flake database."""
        if FLAKE_DB_FILE.exists():
            try:
                with FLAKE_DB_FILE.open("r") as f:
                    return json.load(f)
            except:
                pass
        return {"test_results": {}, "flake_counts": {}}
    
    def _load_quarantined_tests(self) -> Set[str]:
        """Load quarantined tests."""
        if QUARANTINE_FILE.exists():
            try:
                with QUARANTINE_FILE.open("r") as f:
                    data = json.load(f)
                    return set(data.get("quarantined", []))
            except:
                pass
        return set()
    
    def _save_flake_db(self):
        """Save flake database."""
        FLAKE_DB_FILE.parent.mkdir(parents=True, exist_ok=True)
        with FLAKE_DB_FILE.open("w") as f:
            json.dump(self.flake_db, f, indent=2)
    
    def _save_quarantined_tests(self):
        """Save quarantined tests."""
        QUARANTINE_FILE.parent.mkdir(parents=True, exist_ok=True)
        with QUARANTINE_FILE.open("w") as f:
            json.dump({"quarantined": list(self.quarantined_tests)}, f, indent=2)
    
    def record_test_result(self, test_name: str, passed: bool, run_id: str):
        """Record test result."""
        if test_name not in self.flake_db["test_results"]:
            self.flake_db["test_results"][test_name] = []
        
        self.flake_db["test_results"][test_name].append({
            "passed": passed,
            "run_id": run_id,
            "timestamp": self._get_timestamp()
        })
        
        # Update flake count
        if not passed:
            self.flake_db["flake_counts"][test_name] = self.flake_db["flake_counts"].get(test_name, 0) + 1
        
        self._save_flake_db()
    
    def detect_flakes(self) -> List[str]:
        """Detect flaky tests."""
        flaky_tests = []
        
        for test_name, results in self.flake_db["test_results"].items():
            if len(results) < 3:  # Need at least 3 runs to detect flakes
                continue
            
            # Check for inconsistent results
            pass_count = sum(1 for r in results if r["passed"])
            total_count = len(results)
            
            # Test is flaky if it has both passes and failures
            if 0 < pass_count < total_count:
                flake_count = self.flake_db["flake_counts"].get(test_name, 0)
                if flake_count >= FLAKE_THRESHOLD:
                    flaky_tests.append(test_name)
        
        return flaky_tests
    
    def quarantine_test(self, test_name: str):
        """Quarantine a flaky test."""
        self.quarantined_tests.add(test_name)
        self._save_quarantined_tests()
        print(f"🚨 Quarantined flaky test: {test_name}")
    
    def unquarantine_test(self, test_name: str):
        """Unquarantine a test."""
        self.quarantined_tests.discard(test_name)
        self._save_quarantined_tests()
        print(f"✅ Unquarantined test: {test_name}")
    
    def get_quarantined_tests(self) -> Set[str]:
        """Get list of quarantined tests."""
        return self.quarantined_tests.copy()
    
    def generate_flake_report(self) -> Dict[str, Any]:
        """Generate flake report."""
        report = {
            "total_tests": len(self.flake_db["test_results"]),
            "quarantined_tests": len(self.quarantined_tests),
            "flaky_tests": [],
            "flake_stats": {}
        }
        
        for test_name, results in self.flake_db["test_results"].items():
            if len(results) < 3:
                continue
            
            pass_count = sum(1 for r in results if r["passed"])
            total_count = len(results)
            flake_count = self.flake_db["flake_counts"].get(test_name, 0)
            
            if 0 < pass_count < total_count:
                report["flaky_tests"].append({
                    "test_name": test_name,
                    "pass_rate": pass_count / total_count,
                    "flake_count": flake_count,
                    "total_runs": total_count
                })
        
        # Sort by flake count
        report["flaky_tests"].sort(key=lambda x: x["flake_count"], reverse=True)
        
        return report
    
    def _get_timestamp(self) -> str:
        """Get current timestamp."""
        import time
        return time.strftime("%Y-%m-%d %H:%M:%S")
    
    def run_tests_with_rerun(self, test_markers: str = "phase6_perf or phase8_e2e", max_reruns: int = 1):
        """Run tests with automatic rerun on failure."""
        print(f"🔥 Running tests with flake detection: {test_markers}")
        
        # First run
        result1 = self._run_pytest(test_markers)
        
        # If tests failed, try rerun
        if result1["failed_tests"]:
            print(f"⏳ Rerunning {len(result1['failed_tests'])} failed tests...")
            result2 = self._run_pytest(test_markers, rerun_failures=True)
            
            # Merge results
            for test_name in result1["failed_tests"]:
                if test_name in result2["passed_tests"]:
                    print(f"✅ Test {test_name} passed on rerun")
                else:
                    print(f"❌ Test {test_name} failed on rerun")
        
        return result1
    
    def _run_pytest(self, test_markers: str, rerun_failures: bool = False) -> Dict[str, Any]:
        """Run pytest and return results."""
        cmd = ["python", "-m", "pytest", "-m", test_markers, "-v", "--tb=short"]
        
        if rerun_failures:
            cmd.extend(["--rerun-failures", "1"])
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
            
            # Parse results
            passed_tests = []
            failed_tests = []
            
            for line in result.stdout.split('\n'):
                if " PASSED " in line:
                    test_name = self._extract_test_name(line)
                    if test_name:
                        passed_tests.append(test_name)
                elif " FAILED " in line:
                    test_name = self._extract_test_name(line)
                    if test_name:
                        failed_tests.append(test_name)
            
            return {
                "passed_tests": passed_tests,
                "failed_tests": failed_tests,
                "return_code": result.returncode,
                "stdout": result.stdout,
                "stderr": result.stderr
            }
            
        except subprocess.TimeoutExpired:
            return {
                "passed_tests": [],
                "failed_tests": [],
                "return_code": -1,
                "stdout": "",
                "stderr": "Test run timed out"
            }
    
    def _extract_test_name(self, line: str) -> str:
        """Extract test name from pytest output line."""
        # Simple extraction - in production, use more robust parsing
        if "::" in line:
            parts = line.split("::")
            if len(parts) >= 2:
                return parts[-1].strip()
        return ""

def main():
    """Main function."""
    detector = FlakeDetector()
    
    if len(sys.argv) < 2:
        print("Usage: python scripts/flake_detector.py [command] [args...]")
        print("Commands:")
        print("  detect - Detect flaky tests")
        print("  quarantine <test_name> - Quarantine a test")
        print("  unquarantine <test_name> - Unquarantine a test")
        print("  report - Generate flake report")
        print("  run - Run tests with flake detection")
        return
    
    command = sys.argv[1]
    
    if command == "detect":
        flaky_tests = detector.detect_flakes()
        if flaky_tests:
            print(f"🚨 Detected {len(flaky_tests)} flaky tests:")
            for test in flaky_tests:
                print(f"  - {test}")
                detector.quarantine_test(test)
        else:
            print("✅ No flaky tests detected")
    
    elif command == "quarantine":
        if len(sys.argv) < 3:
            print("❌ Test name required")
            return
        test_name = sys.argv[2]
        detector.quarantine_test(test_name)
    
    elif command == "unquarantine":
        if len(sys.argv) < 3:
            print("❌ Test name required")
            return
        test_name = sys.argv[2]
        detector.unquarantine_test(test_name)
    
    elif command == "report":
        report = detector.generate_flake_report()
        print(f"📊 Flake Report:")
        print(f"  Total tests: {report['total_tests']}")
        print(f"  Quarantined tests: {report['quarantined_tests']}")
        print(f"  Flaky tests: {len(report['flaky_tests'])}")
        
        if report["flaky_tests"]:
            print("\n🚨 Flaky tests:")
            for test in report["flaky_tests"][:10]:  # Show top 10
                print(f"  - {test['test_name']}: {test['pass_rate']:.1%} pass rate, {test['flake_count']} flakes")
    
    elif command == "run":
        test_markers = sys.argv[2] if len(sys.argv) > 2 else "phase6_perf or phase8_e2e"
        detector.run_tests_with_rerun(test_markers)
    
    else:
        print(f"❌ Unknown command: {command}")

if __name__ == "__main__":
    main()

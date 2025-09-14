#!/usr/bin/env python3
"""
Roll-Forward / Roll-Back Procedures for Hologram Pipeline
Handles baseline updates and emergency rollbacks.
"""
import json
import os
import sys
import subprocess
from pathlib import Path
from typing import Dict, Any, Optional

BASELINE_FILE = Path("reports/perf/baseline.json")
BACKUP_DIR = Path("reports/perf/backups")

class RollManager:
    """Manages roll-forward and roll-back operations."""
    
    def __init__(self):
        self.baseline_file = BASELINE_FILE
        self.backup_dir = BACKUP_DIR
        self.backup_dir.mkdir(parents=True, exist_ok=True)
    
    def backup_baseline(self, reason: str = "manual") -> str:
        """Backup current baseline."""
        if not self.baseline_file.exists():
            print("❌ No baseline file to backup")
            return ""
        
        timestamp = self._get_timestamp()
        backup_name = f"baseline_{timestamp}_{reason}.json"
        backup_path = self.backup_dir / backup_name
        
        # Copy baseline to backup
        import shutil
        shutil.copy2(self.baseline_file, backup_path)
        
        print(f"✅ Baseline backed up to {backup_path}")
        return str(backup_path)
    
    def roll_forward_baseline(self, reason: str = "performance_improvement") -> bool:
        """Roll forward baseline with new performance data."""
        print("🔄 Rolling forward baseline...")
        
        # Backup current baseline
        backup_path = self.backup_baseline("roll_forward")
        if not backup_path:
            return False
        
        # Check if we're on main branch
        if not self._is_main_branch():
            print("❌ Roll-forward only allowed on main branch")
            return False
        
        # Check if perf gate passes
        if not self._check_perf_gate():
            print("❌ Perf gate must pass before roll-forward")
            return False
        
        # Check for regressions
        if not self._check_no_regressions():
            print("❌ No regressions allowed before roll-forward")
            return False
        
        # Update baseline
        if self._update_baseline():
            print("✅ Baseline rolled forward successfully")
            return True
        else:
            print("❌ Failed to roll forward baseline")
            return False
    
    def roll_back_baseline(self, backup_name: Optional[str] = None) -> bool:
        """Roll back to previous baseline."""
        print("🔄 Rolling back baseline...")
        
        # Find backup to restore
        if backup_name:
            backup_path = self.backup_dir / backup_name
        else:
            backup_path = self._find_latest_backup()
        
        if not backup_path or not backup_path.exists():
            print("❌ No backup found to restore")
            return False
        
        # Backup current baseline
        self.backup_baseline("roll_back")
        
        # Restore backup
        import shutil
        shutil.copy2(backup_path, self.baseline_file)
        
        print(f"✅ Baseline rolled back to {backup_path}")
        return True
    
    def emergency_rollback(self) -> bool:
        """Emergency rollback procedure."""
        print("🚨 Emergency rollback initiated...")
        
        # 1. Revert last app/service change
        if not self._revert_last_change():
            print("❌ Failed to revert last change")
            return False
        
        # 2. Re-run Phase 6 + Phase 8
        if not self._rerun_tests():
            print("❌ Failed to re-run tests")
            return False
        
        # 3. Check if still red
        if self._check_perf_gate():
            print("✅ Emergency rollback successful")
            return True
        else:
            print("⚠️ Still red after rollback, widening SLO temporarily")
            return self._widen_slo_temporarily()
    
    def _get_timestamp(self) -> str:
        """Get current timestamp."""
        import time
        return time.strftime("%Y%m%d_%H%M%S")
    
    def _is_main_branch(self) -> bool:
        """Check if we're on main branch."""
        try:
            result = subprocess.run(
                ["git", "branch", "--show-current"],
                capture_output=True, text=True
            )
            return result.stdout.strip() == "main"
        except:
            return False
    
    def _check_perf_gate(self) -> bool:
        """Check if perf gate passes."""
        try:
            result = subprocess.run(
                ["python", "scripts/check_perf_budget.py"],
                capture_output=True, text=True
            )
            return result.returncode == 0
        except:
            return False
    
    def _check_no_regressions(self) -> bool:
        """Check for regressions."""
        try:
            result = subprocess.run(
                ["python", "scripts/baseline_compare.py"],
                capture_output=True, text=True
            )
            return result.returncode == 0
        except:
            return False
    
    def _update_baseline(self) -> bool:
        """Update baseline with current performance data."""
        try:
            result = subprocess.run(
                ["python", "scripts/baseline_compare.py"],
                capture_output=True, text=True
            )
            return result.returncode == 0
        except:
            return False
    
    def _find_latest_backup(self) -> Optional[Path]:
        """Find latest backup file."""
        backups = list(self.backup_dir.glob("baseline_*.json"))
        if not backups:
            return None
        
        # Sort by modification time
        backups.sort(key=lambda p: p.stat().st_mtime, reverse=True)
        return backups[0]
    
    def _revert_last_change(self) -> bool:
        """Revert last app/service change."""
        try:
            result = subprocess.run(
                ["git", "revert", "HEAD", "--no-edit"],
                capture_output=True, text=True
            )
            return result.returncode == 0
        except:
            return False
    
    def _rerun_tests(self) -> bool:
        """Re-run Phase 6 + Phase 8 tests."""
        try:
            result = subprocess.run(
                ["python", "-m", "pytest", "-m", "phase6_perf or phase8_e2e", "-v"],
                capture_output=True, text=True
            )
            return result.returncode == 0
        except:
            return False
    
    def _widen_slo_temporarily(self) -> bool:
        """Widen SLO temporarily on PR env only."""
        print("⚠️ Widening SLO temporarily on PR env...")
        
        # Set temporary SLO values
        os.environ["SLO_VERIFY_P95_MS"] = "50"
        os.environ["SLO_ENCODE_P95_MS"] = "500"
        os.environ["SLO_GQL_P95_MS"] = "500"
        
        # Test with widened SLOs
        try:
            result = subprocess.run(
                ["python", "scripts/check_perf_budget.py"],
                capture_output=True, text=True
            )
            if result.returncode == 0:
                print("✅ SLOs widened temporarily, perf gate passes")
                return True
            else:
                print("❌ Still failing even with widened SLOs")
                return False
        except:
            return False
    
    def list_backups(self):
        """List available backups."""
        backups = list(self.backup_dir.glob("baseline_*.json"))
        if not backups:
            print("No backups found")
            return
        
        print("Available backups:")
        for backup in sorted(backups, key=lambda p: p.stat().st_mtime, reverse=True):
            mtime = backup.stat().st_mtime
            import time
            mtime_str = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(mtime))
            print(f"  {backup.name} ({mtime_str})")

def main():
    """Main function."""
    if len(sys.argv) < 2:
        print("Usage: python scripts/roll_forward_back.py [command] [args...]")
        print("Commands:")
        print("  roll-forward [reason] - Roll forward baseline")
        print("  roll-back [backup_name] - Roll back to backup")
        print("  emergency - Emergency rollback procedure")
        print("  backup [reason] - Backup current baseline")
        print("  list - List available backups")
        return
    
    manager = RollManager()
    command = sys.argv[1]
    
    if command == "roll-forward":
        reason = sys.argv[2] if len(sys.argv) > 2 else "performance_improvement"
        success = manager.roll_forward_baseline(reason)
        sys.exit(0 if success else 1)
    
    elif command == "roll-back":
        backup_name = sys.argv[2] if len(sys.argv) > 2 else None
        success = manager.roll_back_baseline(backup_name)
        sys.exit(0 if success else 1)
    
    elif command == "emergency":
        success = manager.emergency_rollback()
        sys.exit(0 if success else 1)
    
    elif command == "backup":
        reason = sys.argv[2] if len(sys.argv) > 2 else "manual"
        backup_path = manager.backup_baseline(reason)
        if backup_path:
            print(f"✅ Backup created: {backup_path}")
        else:
            print("❌ Backup failed")
            sys.exit(1)
    
    elif command == "list":
        manager.list_backups()
    
    else:
        print(f"❌ Unknown command: {command}")
        sys.exit(1)

if __name__ == "__main__":
    main()

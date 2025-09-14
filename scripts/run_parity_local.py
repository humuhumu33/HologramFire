import json, subprocess, sys, os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "bridge" / "cli.js"

def main(hex_payload: str):
  proc = subprocess.run(
    ["node", str(BRIDGE), "proc:uorid_hex", hex_payload],
    cwd=str(ROOT), capture_output=True, text=True, check=True)
  print(proc.stdout)

if __name__ == "__main__":
  if len(sys.argv) != 2:
    print("usage: python scripts/run_parity_local.py <hex>")
    sys.exit(2)
  main(sys.argv[1])

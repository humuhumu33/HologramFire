# Generates vectors/r96/golden.json from real prod code via the bridge.
import json, os, sys
from pathlib import Path

# Add the project root to the Python path
sys.path.insert(0, str(Path(__file__).parent.parent))

from tests._helpers import bridge_call

def main():
    out = {str(b): bridge_call("atlas:r96", str(b))["class"] for b in range(256)}
    vec_dir = Path("vectors/r96")
    vec_dir.mkdir(parents=True, exist_ok=True)
    (vec_dir / "golden.json").write_text(json.dumps(out, indent=2, sort_keys=True))
    print("Wrote vectors/r96/golden.json with 256 entries.")

if __name__ == "__main__":
    main()

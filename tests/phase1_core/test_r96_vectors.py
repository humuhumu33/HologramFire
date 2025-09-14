import json
from pathlib import Path
import pytest
from tests._helpers import bridge_call

pytestmark = pytest.mark.phase1_core

GOLDEN = Path("vectors/r96/golden.json")

def test_r96_golden_present():
    assert GOLDEN.exists(), "Run: python scripts/gen_vectors_phase1.py"

def test_r96_matches_golden():
    gold = json.loads(GOLDEN.read_text())
    for b_str, cls in gold.items():
        b = int(b_str)
        res = bridge_call("atlas:r96", str(b))
        assert res["ok"] is True
        assert res["class"] == cls, f"Byte {b} expected {cls}, got {res['class']}"

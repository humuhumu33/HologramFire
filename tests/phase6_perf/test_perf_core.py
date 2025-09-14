import os, pytest
from tests.phase6_perf._perf_utils import measure, write_csv

pytestmark = pytest.mark.phase6_perf

# Env overrides for thresholds
ENCODE_P95_MS = float(os.getenv("SLO_ENCODE_P95_MS", "100"))
VERIFY_P95_MS = float(os.getenv("SLO_VERIFY_P95_MS", "10"))
ENC_MB         = int(os.getenv("ENC_MB", "1"))  # payload size for encode test

def deterministic_payload(n):
    return bytes((i % 256 for i in range(n)))

def _has_atlas(atlas_api):
    return callable(atlas_api.get("encode")) and callable(atlas_api.get("verify"))

def test_verify_p95_under_slo(atlas_api):
    if not _has_atlas(atlas_api):
        pytest.skip("Atlas encode/verify not available in this build")

    # Build a valid state via encode
    data = deterministic_payload(256*256)  # 64KB to keep test quick & stable
    state = atlas_api["encode"](data)

    stats = measure(atlas_api["verify"], state, warmup=10, runs=60)
    csv = write_csv([["core","verify_ms", f"{stats['p50']:.3f}", f"{stats['p95']:.3f}",
                      f"{stats['p99']:.3f}", f"{stats['avg']:.3f}", stats["n"], "atlas.verify"]],
                    "core_perf.csv")

    assert stats["p95"] < VERIFY_P95_MS, (
        f"verify p95={stats['p95']:.2f}ms exceeds {VERIFY_P95_MS}ms (CSV: {csv})"
    )

def test_encode_p95_under_slo(atlas_api):
    if not _has_atlas(atlas_api):
        pytest.skip("Atlas encode/verify not available in this build")

    size = ENC_MB * 1024 * 1024
    data = deterministic_payload(size)

    stats = measure(atlas_api["encode"], data, warmup=5, runs=30)
    csv = write_csv([["core",f"encode_{ENC_MB}MB_ms", f"{stats['p50']:.3f}", f"{stats['p95']:.3f}",
                      f"{stats['p99']:.3f}", f"{stats['avg']:.3f}", stats["n"], f"atlas.encode {ENC_MB}MB"]],
                    "core_perf.csv")

    assert stats["p95"] < ENCODE_P95_MS, (
        f"encode p95={stats['p95']:.2f}ms for {ENC_MB}MB exceeds {ENCODE_P95_MS}ms (CSV: {csv})"
    )

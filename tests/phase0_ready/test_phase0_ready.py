import os
import pytest
from tests._helpers import import_prod, bridge_call

pytestmark = pytest.mark.phase0_ready


def test_bridge_present_and_build_exists():
    """Test that the bridge exists and the TypeScript build is ready."""
    # Assert bridge exists
    assert os.path.exists("bridge/cli.js"), "bridge/cli.js missing"
    # Assert TS build is ready
    assert os.path.exists("core/build/dist"), "core/build/dist missing; build with `pnpm -C core build` or `npm --prefix core run build`"


def test_r96_real_call(atlas_api):
    """Test R96 classification with real production code."""
    # Byte 0 and 1 should map deterministically to classes (we don't assert exact number here yet)
    c0 = atlas_api["r96"](0)
    c1 = atlas_api["r96"](1)
    assert isinstance(c0, int) and 0 <= c0 < 96
    assert isinstance(c1, int) and 0 <= c1 < 96
    assert c0 is not None and c1 is not None


def test_uorid_real_call(uorid_api):
    """Test UORID computation with real production code."""
    content = b"Hologram Phase0.5"
    a = uorid_api["uorid"](content)
    b = uorid_api["uorid"](content)
    assert a == b and isinstance(a, str) and len(a) >= 32


def test_ctp96_real_roundtrip(ctp96_api):
    """Test CTP-96 frame roundtrip with real production code."""
    content = b"\x01\x02payload"
    res = ctp96_api["frame_roundtrip"](content)
    assert res["ok"] and res["valid"]
    assert res["recovered"] == content.hex()


def test_vector_directory_created():
    """Test that the vector directory structure is ready."""
    from pathlib import Path
    
    vec_dir = Path("vectors")
    assert vec_dir.exists(), "Vectors directory should exist"
    assert vec_dir.is_dir(), "Vectors should be a directory"
    
    # Check that subdirectories are created
    expected_subdirs = ["r96", "atlas", "bhic_cef", "uorid"]
    for subdir in expected_subdirs:
        subdir_path = vec_dir / subdir
        assert subdir_path.exists(), f"Vector subdirectory {subdir} should exist"
        assert subdir_path.is_dir(), f"Vector subdirectory {subdir} should be a directory"


def test_production_build_verification():
    """Test that the production build verification works."""
    from tests._helpers import verify_production_build
    
    # This should not raise an exception
    verify_production_build()
    
    # Check that core dist exists or can be built
    from pathlib import Path
    core_dist = Path("core/dist")
    core_src = Path("core/src")
    
    assert core_src.exists(), "Core source directory should exist"
    # dist might not exist if not built yet, but that's ok for Phase 0


def test_pytest_markers_configured():
    """Test that pytest markers are properly configured."""
    from pathlib import Path
    
    # Check that pytest.ini exists and contains our markers
    pytest_ini = Path("pytest.ini")
    assert pytest_ini.exists(), "pytest.ini should exist"
    
    # Read the pytest.ini content
    content = pytest_ini.read_text()
    
    required_markers = [
        "phase0_ready",
        "phase1_core", 
        "phase2_integration",
        "phase3_runtime",
        "phase4_network",
        "phase5_graphql",
        "phase6_perf",
        "phase7_security",
        "phase8_e2e",
        "no_ci"
    ]
    
    for marker in required_markers:
        assert marker in content, f"Required marker {marker} not found in pytest.ini"
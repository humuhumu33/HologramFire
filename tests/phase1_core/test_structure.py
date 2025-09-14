import pytest
import json
from pathlib import Path

pytestmark = pytest.mark.phase1_core

def test_bridge_exists():
    """Test that the bridge CLI exists and is executable."""
    bridge_path = Path("bridge/cli.js")
    assert bridge_path.exists(), "Bridge CLI should exist at bridge/cli.js"
    
    # Check that it's a valid JavaScript file
    content = bridge_path.read_text()
    assert "#!/usr/bin/env node" in content, "Bridge should be a Node.js script"
    assert "atlas:r96" in content, "Bridge should support atlas:r96 command"
    assert "atlas:encode" in content, "Bridge should support atlas:encode command"
    assert "atlas:decode" in content, "Bridge should support atlas:decode command"
    assert "atlas:verify" in content, "Bridge should support atlas:verify command"
    assert "atlas:witnesses" in content, "Bridge should support atlas:witnesses command"

def test_core_build_exists():
    """Test that the core build directory exists."""
    build_path = Path("core/build/dist")
    assert build_path.exists(), "Core build directory should exist"
    
    # Check for key modules
    r96_path = build_path / "src/core/resonance/R96.js"
    assert r96_path.exists(), "R96 module should be built"
    
    atlas_path = build_path / "src/atlas12288/Atlas12288Encoder.js"
    assert atlas_path.exists(), "Atlas encoder should be built"
    
    uorid_path = build_path / "src/identity/UORID.js"
    assert uorid_path.exists(), "UORID module should be built"

def test_phase1_test_structure():
    """Test that Phase 1 test structure is correct."""
    test_dir = Path("tests/phase1_core")
    assert test_dir.exists(), "Phase 1 test directory should exist"
    
    test_files = ["test_core.py", "test_r96_vectors.py", "test_structure.py"]
    for test_file in test_files:
        test_path = test_dir / test_file
        assert test_path.exists(), f"Test file {test_file} should exist"

def test_scripts_directory():
    """Test that scripts directory exists with vector generator."""
    scripts_dir = Path("scripts")
    assert scripts_dir.exists(), "Scripts directory should exist"
    
    gen_script = scripts_dir / "gen_vectors_phase1.py"
    assert gen_script.exists(), "Vector generator script should exist"
    
    # Check script content
    content = gen_script.read_text()
    assert "bridge_call" in content, "Script should use bridge_call"
    assert "atlas:r96" in content, "Script should call atlas:r96"

def test_conftest_extensions():
    """Test that conftest.py has been extended with Phase 1 fixtures."""
    conftest_path = Path("tests/conftest.py")
    assert conftest_path.exists(), "conftest.py should exist"
    
    content = conftest_path.read_text()
    assert "json_dumps" in content, "conftest should have json_dumps helper"
    assert "atlas:encode" in content, "conftest should support atlas:encode"
    assert "atlas:decode" in content, "conftest should support atlas:decode"
    assert "atlas:verify" in content, "conftest should support atlas:verify"
    assert "atlas:witnesses" in content, "conftest should support atlas:witnesses"

def test_vectors_directory():
    """Test that vectors directory exists."""
    vectors_dir = Path("vectors")
    assert vectors_dir.exists(), "Vectors directory should exist"
    
    r96_dir = vectors_dir / "r96"
    assert r96_dir.exists(), "R96 vectors directory should exist"

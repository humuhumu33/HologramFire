import json, os, platform, subprocess, shutil, uuid, pytest
from pathlib import Path

pytestmark = pytest.mark.phase3_runtime

ROOT = Path(__file__).resolve().parents[2]  # repo root
BRIDGE = ROOT / "bridge" / "cli.js"

SMALL_HEX = bytes(range(256)).hex()  # keep small to avoid Windows arg limits

def have(cmd):
    return shutil.which(cmd) is not None

def run_node_local(hex_payload: str):
    assert BRIDGE.exists(), "bridge/cli.js missing"
    proc = subprocess.run(
        ["node", str(BRIDGE), "proc:uorid_hex", hex_payload],
        cwd=str(ROOT),
        capture_output=True, text=True, check=True
    )
    out = json.loads(proc.stdout or "{}")
    assert out.get("ok") is True, out
    return out["digest"]

def run_docker_node(hex_payload: str):
    if not have("docker"):
        pytest.skip("docker not available")
    # Mount repo into container and call the same bridge
    work = str(ROOT).replace("\\", "/")
    cmd = [
        "docker","run","--rm",
        "-v", f"{work}:/work",
        "-w","/work",
        "node:18-alpine",
        "node","bridge/cli.js","proc:uorid_hex", hex_payload
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=True)
    out = json.loads(proc.stdout or "{}")
    assert out.get("ok") is True, out
    return out["digest"]

def run_external(cmd_var: str, hex_payload: str):
    """
    Optional adapters for WASM/EFI/U-Boot. 
    Set env to a full command that prints JSON: {"ok":true,"digest":"..."}
      RUNTIME_CMD_WASM
      RUNTIME_CMD_EFI
      RUNTIME_CMD_UBOOT
    """
    cmd = os.getenv(cmd_var)
    if not cmd:
        pytest.skip(f"{cmd_var} not set")
    # Allow space-separated command string; append hex payload
    parts = cmd.split() + [hex_payload]
    proc = subprocess.run(parts, capture_output=True, text=True, check=True)
    out = json.loads(proc.stdout or "{}")
    assert out.get("ok") is True, out
    return out["digest"]

def test_node_vs_docker_parity():
    d1 = run_node_local(SMALL_HEX)
    d2 = run_docker_node(SMALL_HEX)
    assert d1 == d2, f"Digest mismatch:\n local={d1}\n docker={d2}"

def test_node_vs_wasm_parity():
    d1 = run_node_local(SMALL_HEX)
    d2 = run_external("RUNTIME_CMD_WASM", SMALL_HEX)
    assert d1 == d2

def test_node_vs_efi_parity():
    d1 = run_node_local(SMALL_HEX)
    d2 = run_external("RUNTIME_CMD_EFI", SMALL_HEX)
    assert d1 == d2

def test_node_vs_uboot_parity():
    d1 = run_node_local(SMALL_HEX)
    d2 = run_external("RUNTIME_CMD_UBOOT", SMALL_HEX)
    assert d1 == d2

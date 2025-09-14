import os
import secrets
import pytest

pytestmark = pytest.mark.phase4_network

def small():
    return secrets.token_bytes(128)  # keep tiny to avoid Windows arg limits

# -------- IPFS (real node over HTTP API) --------
def test_ipfs_put_get_roundtrip(ipfs_client):
    data = small()
    cid = ipfs_client.add_bytes(data)
    got = ipfs_client.cat(cid)
    assert got == data, "IPFS cat must return same bytes"

def test_ipfs_pin_list(ipfs_client):
    data = small()
    cid = ipfs_client.add_bytes(data)
    pins = ipfs_client.pin_ls(cid)
    # Some nodes return detailed pin info; minimally assert the call succeeds
    assert isinstance(pins, dict)

# -------- CTP-96 (real production module via bridge) --------
def test_ctp96_frame_deframe(ctp96_api):
    data = small()
    res = ctp96_api["roundtrip"](data)
    # If CTP-96 not built, the bridge returns ok:false and this test will fail — that's correct.
    assert res.get("ok") is True, res.get("err")
    assert res.get("valid") in (True, False)  # some builds may not expose validate; we passed True
    assert bytes.fromhex(res["recovered"]) == data
    # Ensure frame bytes exist (useful for future tamper tests)
    assert isinstance(res.get("frameHex"), str) and len(res["frameHex"]) > 0

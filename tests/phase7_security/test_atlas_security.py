import pytest
from tests.phase7_security._sec_utils import has_atlas, flip_one_bit

pytestmark = pytest.mark.phase7_security

def test_tamper_rejected(atlas_api):
    if not has_atlas(atlas_api):
        pytest.skip("Atlas not available")
    data = b"A" * 4096
    state = atlas_api["encode"](data)
    assert atlas_api["verify"](state), "sanity: encoded state must verify"

    # flip a single bit in [0,0]
    tampered = [row[:] for row in state]
    tampered[0][0] = (int(tampered[0][0]) ^ 0x01) & 0xFF

    assert not atlas_api["verify"](tampered), "single-bit flip must be detected"

def test_witness_mismatch_fails(atlas_api):
    if not has_atlas(atlas_api):
        pytest.skip("Atlas not available")
    data = b"B" * 4096
    state = atlas_api["encode"](data)
    wres = atlas_api["witnesses"](state)
    assert wres["ok"] and wres["valid"]

    # tamper state but reuse older witnesses
    tampered = [row[:] for row in state]
    tampered[0][1] = (int(tampered[0][1]) ^ 0x02) & 0xFF

    # Expect validate to fail on mismatched witnesses
    v = atlas_api["witnesses"](tampered)
    assert v["ok"] and v["valid"]  # witnesses match tampered state
    assert not atlas_api["verify"](tampered), "tampered state should still fail overall verification"

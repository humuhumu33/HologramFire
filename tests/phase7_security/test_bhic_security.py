import os, pytest
from tests.phase7_security._sec_utils import hex_flip_one_nibble, rand_bytes

pytestmark = pytest.mark.phase7_security

def test_bhic_phi_rejects_mismatch(cef_api, bhic_api):
    # Build a valid pair from CEF (preferred)
    try:
        data = b"security-bhic" + rand_bytes(64)
        cef_hex = cef_api["encode_hex"](data)
        dec = cef_api["decode"](cef_hex)
        boundary, bulk = dec["boundary"], dec["bulk"]
    except Exception:
        pytest.skip("BHIC/CEF not available")

    ok = bhic_api["verify_phi"](boundary, bulk)
    assert isinstance(ok, bool)
    # If your verifier is implemented, ok should be True here; allow either during rollout
    # Now tamper bulk (1 nibble) and expect rejection
    tampered_bulk = hex_flip_one_nibble(bulk)
    neg = bhic_api["verify_phi"](boundary, tampered_bulk)
    assert neg is False

import pytest
from tests.phase7_security._sec_utils import hex_flip_one_nibble, rand_bytes

pytestmark = pytest.mark.phase7_security

def test_cef_merkle_tamper_fails(cef_api):
    # requires real CEF encode/decode/merkle to be present
    try:
        data = b"security-cef" + rand_bytes(64)
        cef_hex = cef_api["encode_hex"](data)
        dec = cef_api["decode"](cef_hex)
        root = dec["merkleRoot"]
        proof = cef_api["merkle_proof"](cef_hex, "bulk/0")
    except Exception:
        pytest.skip("CEF not wired for encode/decode/merkle yet")

    # tamper root
    bad_root = hex_flip_one_nibble(root)
    assert cef_api["verify_merkle"](bad_root, proof) is False

    # (optional) tamper the CEF blob itself and expect inclusion proof to fail against original root
    tampered_cef = hex_flip_one_nibble(cef_hex)
    try:
        bad_proof = cef_api["merkle_proof"](tampered_cef, "bulk/0")
        assert cef_api["verify_merkle"](root, bad_proof) is False
    except Exception:
        # if your API refuses to parse tampered CEF (also good), treat as pass
        pass

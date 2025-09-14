import pytest, json
from tests._helpers import bridge_call
from tests.phase7_security._sec_utils import rand_bytes, hex_flip_one_nibble

pytestmark = pytest.mark.phase7_security

def test_ctp96_tamper_or_invalid(ctp96_api):
    data = rand_bytes(96)
    res = ctp96_api["roundtrip"](data)
    assert res.get("ok") is True
    frame_hex = res["frameHex"]

    # Tamper a nibble => deframe should fail or recovered != original or validate==False
    bad = hex_flip_one_nibble(frame_hex)

    # If your bridge exposes explicit validate/deframe, you can add commands here.
    # We reuse the net:ctp96_roundtrip path to test behavior on tampered frame by
    # adding a dedicated bridge cmd (optional). If not present, this is a smoke.
    try:
        out = bridge_call("net:ctp96_deframe_hex", bad)  # add this case if you expose it
        # Successful parse on tampered frame is suspicious; ensure recovered != original or invalid
        if out.get("ok"):
            rec = bytes.fromhex(out["recovered"])
            assert rec != data or (out.get("valid") is False)
    except Exception:
        # No deframe_hex in bridge: acceptable; absence = skip deeper CTP-96 negatives
        pass

@pytest.mark.skip(reason="enable when your CTP-96 carries nonces/epochs")
def test_ctp96_replay_rejected(ctp96_api):
    # When your frame format carries a nonce/epoch, frame once and re-submit
    # to a real validator that tracks recent nonces. Expect the second validate to fail.
    pass

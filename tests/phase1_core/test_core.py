import pytest
import random

pytestmark = pytest.mark.phase1_core

def sum_mod256_rows_cols(state):
    rows = len(state)
    cols = len(state[0]) if rows else 0
    # column sums (cycles)
    col_sums = [0]*cols
    row_sums = [0]*rows
    for r in range(rows):
        acc = 0
        for c in range(cols):
            v = int(state[r][c]) & 0xFF
            acc = (acc + v) & 0xFF
            col_sums[c] = (col_sums[c] + v) & 0xFF
        row_sums[r] = acc
    return row_sums, col_sums

def deterministic_payload(n=1024):
    # stable byte pattern for reproducible states
    return bytes((i % 256 for i in range(n)))

def flip_one_bit(state, r=0, c=0, bit=0):
    new = [row[:] for row in state]
    new[r][c] = (int(new[r][c]) ^ (1 << bit)) & 0xFF
    return new

def test_conservation_on_encoded_state(atlas_api):
    data = deterministic_payload()
    state = atlas_api["encode"](data)
    assert atlas_api["verify"](state), "Encoded state must verify"
    row_sums, col_sums = sum_mod256_rows_cols(state)
    assert all(s == 0 for s in row_sums), "All row sums must be 0 mod 256"
    assert all(s == 0 for s in col_sums), "All col sums must be 0 mod 256"

def test_minimal_tamper_breaks_conservation(atlas_api):
    data = deterministic_payload()
    state = atlas_api["encode"](data)
    tampered = flip_one_bit(state, 0, 0, 0)
    assert not atlas_api["verify"](tampered), "Single-bit flip must be detected"

def test_encode_decode_idempotence(atlas_api):
    data = deterministic_payload(2048)
    state = atlas_api["encode"](data)
    out = atlas_api["decode"](state)
    assert out == data
    # idempotence: encode(decode(encode(x))) == encode(x)
    state2 = atlas_api["encode"](out)
    assert state2 == state

def test_witness_generation_and_validation(atlas_api):
    data = deterministic_payload(4096)
    state = atlas_api["encode"](data)
    wres = atlas_api["witnesses"](state)
    assert wres["ok"] is True
    assert wres["valid"] is True
    w = wres["witnesses"]
    # basic sanity on witness shape (keys are implementation-specific; be lenient)
    assert isinstance(w, dict) and len(w) >= 1

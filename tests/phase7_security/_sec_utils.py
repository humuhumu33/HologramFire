import os, secrets, random

def rand_bytes(n=128):
    return secrets.token_bytes(n)

def flip_one_bit(b: bytes, bit_index: int = 0) -> bytes:
    if not b: return b
    i = min(len(b)-1, bit_index // 8)
    mask = 1 << (bit_index % 8)
    arr = bytearray(b); arr[i] ^= mask; return bytes(arr)

def hex_flip_one_nibble(h: str):
    if len(h) == 0: return h
    i = min(len(h)-1, 0)
    return h[:i] + ("0" if h[i] != "0" else "1") + h[i+1:]

def has_atlas(api) -> bool:
    return callable(api.get("encode")) and callable(api.get("verify"))

def env_true(name: str, default=False) -> bool:
    v = os.getenv(name)
    if v is None: return default
    return v.lower() in ("1","true","yes","y","on")

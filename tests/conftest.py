import os
import pathlib
import pytest
import json
import requests
from ._helpers import get_node_hologram_api, call_node_function, verify_production_build, bridge_call


class GraphQLClient:
    def __init__(self, url: str):
        self.url = url
    def query(self, query: str, variables: dict | None = None, headers: dict | None = None):
        payload = {"query": query, "variables": variables or {}}
        r = requests.post(self.url, json=payload, headers=headers or {})
        r.raise_for_status()
        data = r.json()
        if "errors" in data and data["errors"]:
            raise RuntimeError(f"GraphQL errors: {data['errors']}")
        return data["data"]


# Verify production build is available
verify_production_build()

# Get the real production API (optional for Phase 0)
HG = None
try:
    HG = get_node_hologram_api()
except Exception as e:
    print(f"Warning: Could not load production API: {e}")
    print("Phase 0 will test basic structure without full API integration")

# Vectors live here (Phase 1+ will populate)
VEC_DIR = pathlib.Path("vectors")
VEC_DIR.mkdir(parents=True, exist_ok=True)


@pytest.fixture(scope="session")
def atlas_api():
    """
    Map to PRODUCTION functions using the Node.js bridge.
    """
    return {
        "r96":          lambda b: bridge_call("atlas:r96", str(b))["class"],
        "encode":       lambda data: bridge_call("atlas:encode", data.hex())["state"],
        "decode":       lambda state: bytes.fromhex(bridge_call("atlas:decode", json_dumps(state))["hex"]),
        "verify":       lambda state: bridge_call("atlas:verify", json_dumps(state))["valid"],
        "witnesses":    lambda state: bridge_call("atlas:witnesses", json_dumps(state)),
    }

# helper to serialize nested lists safely
def json_dumps(state):
    import json
    return json.dumps(state, separators=(",", ":"))


@pytest.fixture(scope="session")
def cef_api():
    return {
        "encode_hex":   lambda data: bridge_call("cef:encode_hex", data.hex())["cefHex"],
        "decode":       lambda cef_hex: bridge_call("cef:decode", cef_hex),
        "canonicalize": lambda cef_hex: bridge_call("cef:canonical", cef_hex)["cefHex"],
        "merkle_proof": lambda cef_hex, path="bulk/0": bridge_call("cef:merkle_proof", cef_hex, path)["proof"],
        "verify_merkle":lambda root_hex, proof: bridge_call("cef:verify_merkle", root_hex, json.dumps(proof))["valid"],
    }


@pytest.fixture(scope="session")
def bhic_api():
    return {
        "verify_phi": lambda boundary_hex, bulk_hex:
            bridge_call("bhic:verify_phi", boundary_hex, bulk_hex)["valid"]
    }


@pytest.fixture(scope="session")
def uorid_api():
    def compute(data: bytes) -> str:
        res = bridge_call("uorid:compute", data.hex())["id"]
        # Accept object or string
        if isinstance(res, dict):
            return res.get("digest") or json.dumps(res, separators=(",",":"))
        return res
    return {"uorid": compute}


@pytest.fixture(scope="session")
def ctp96_api():
    def roundtrip(data: bytes):
        return bridge_call("net:ctp96_roundtrip", data.hex())
    return {"roundtrip": roundtrip}


@pytest.fixture(scope="session")
def sdk_api():
    return {
        "validate_schema": lambda data: call_node_function("./core/src/proof-chain/index", "validateSchema", data),
        "generate_target": lambda target_type: call_node_function("./core/src/proof-chain/index", "generateTarget", target_type),  # ("wasm"|"efi"|"uboot"|"docker")
        "publish": lambda data: call_node_function("./core/src/proof-chain/index", "publish", data),  # real IPFS if configured
    }


@pytest.fixture(scope="session")
def gql_client():
    url = os.getenv("GRAPHQL_URL")  # e.g. http://localhost:4000/graphql
    if not url:
        pytest.skip("GRAPHQL_URL not set (Phase 5 will skip).")
    return GraphQLClient(url)


@pytest.fixture(scope="session")
def ipfs_client():
    api = os.getenv("IPFS_API")  # e.g., http://127.0.0.1:5001
    if not api:
        pytest.skip("IPFS_API not set (Phase 4 will skip).")
    
    import requests
    
    class IPFS:
        def __init__(self, base): 
            self.base = base.rstrip("/")
        
        def _post(self, path, files=None, params=None):
            url = f"{self.base}{path}"
            r = requests.post(url, files=files, params=params or {})
            r.raise_for_status()
            return r.json()
        
        def _get(self, path, params=None, stream=False):
            url = f"{self.base}{path}"
            r = requests.get(url, params=params or {}, stream=stream)
            r.raise_for_status()
            return r
        
        def add_bytes(self, b: bytes):
            files = {'file': ('blob.bin', b)}
            res = self._post("/api/v0/add", files=files, params={"pin":"true"})
            return res["Hash"]
        
        def cat(self, cid: str) -> bytes:
            r = self._get("/api/v0/cat", params={"arg":cid}, stream=True)
            return r.content
        
        def pin_ls(self, cid: str):
            try:
                return self._get("/api/v0/pin/ls", params={"arg":cid}).json()
            except Exception:
                return {}
    
    return IPFS(api)


@pytest.fixture(scope="session")
def hologram_core():
    """
    Direct access to the core hologram functionality.
    """
    return HG.get("core", {})


@pytest.fixture(scope="session")
def production_version():
    """
    Get the production version string.
    """
    return HG.get("__version__", "unknown")

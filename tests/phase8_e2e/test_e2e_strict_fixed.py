# tests/phase8_e2e/test_e2e_strict_fixed.py
# Fixed Strict E2E: adapted to work with actual GraphQL schema
# Env:
#   IPFS_API     e.g. http://127.0.0.1:5001
#   GRAPHQL_URL  e.g. http://localhost:4000/graphql
#   GRAPHQL_TOKEN (optional) "Bearer <token>"

import os
import io
import json
import time
import uuid
import hashlib
import requests
import pytest

MARK = pytest.mark.phase8_e2e

# ---- helpers ---------------------------------------------------------------

def _env(name: str) -> str:
    v = os.getenv(name, "").strip()
    if not v:
        pytest.skip(f"Missing required env var: {name}")
    return v

def _sha256_hex(b: bytes) -> str:
    h = hashlib.sha256()
    h.update(b)
    return h.hexdigest()

def _ipfs_add(ipfs_api: str, filename: str, data: bytes) -> str:
    url = f"{ipfs_api.rstrip('/')}/api/v0/add"
    # Use multipart/form-data to add a single file; pin=true so it's retained.
    files = {'file': (filename, io.BytesIO(data))}
    r = requests.post(url, params={"pin": "true"}, files=files, timeout=30)
    r.raise_for_status()
    # ipfs add may return one or more JSON lines; take the last valid JSON
    line = r.text.strip().splitlines()[-1]
    obj = json.loads(line)
    cid = obj.get("Hash") or obj.get("hash") or obj.get("Cid") or obj.get("cid")
    assert cid, f"IPFS add returned no CID: {r.text}"
    return cid

def _gql(graphql_url: str, query: str, variables: dict):
    headers = {"content-type": "application/json"}
    token = os.getenv("GRAPHQL_TOKEN", "").strip()
    if token:
        headers["authorization"] = token
    r = requests.post(
        graphql_url,
        headers=headers,
        json={"query": query, "variables": variables},
        timeout=30,
    )
    r.raise_for_status()
    body = r.json()
    if "errors" in body:
        raise AssertionError(f"GraphQL error(s): {body['errors']}")
    return body.get("data")

def _log_event(event_path: str, rec: dict):
    os.makedirs(os.path.dirname(event_path), exist_ok=True)
    rec = {"ts": int(time.time()), **rec}
    with open(event_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, separators=(",", ":")) + "\n")

# ---- the fixed strict test -------------------------------------------------------

@MARK
@pytest.mark.strict
def test_e2e_strict_publish_register_resolve_verify_fixed(tmp_path):
    ipfs_api = _env("IPFS_API")
    graphql_url = _env("GRAPHQL_URL")

    # Where to write audit events (kept very short path for Windows)
    events_path = os.path.join("reports", "e2e", "events.jsonl")
    os.makedirs(os.path.dirname(events_path), exist_ok=True)

    # 1) Prepare a tiny content file (the "thing" we will publish)
    unique = uuid.uuid4().hex[:8]
    name = f"docs/strict-{unique}"  # human-readable name in the catalog
    content = f"Strict E2E demo {unique} @ {int(time.time())}\n"
    content_sha = _sha256_hex(content.encode("utf-8"))

    # 2) Upload file bytes to IPFS → get CID (exact bytes, no re-encoding)
    cid_file = _ipfs_add(ipfs_api, "demo.txt", content.encode("utf-8"))
    _log_event(events_path, {"suite": "phase8_strict_fixed", "event": "ipfs_add_file", "cid": cid_file, "sha256": content_sha})

    # 3) Create a small manifest that declares what this is (canonical JSON)
    manifest_obj = {
        "name": name,
        "kind": "document",
        "mime": "text/plain",
        "size": len(content),
        "sha256": content_sha,
        "cid": cid_file,
        "version": 1,
        "ts": int(time.time())
    }
    manifest_bytes = json.dumps(manifest_obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    manifest_sha = _sha256_hex(manifest_bytes)

    # 4) Upload manifest to IPFS → get manifest CID (tamper-evident)
    cid_manifest = _ipfs_add(ipfs_api, "manifest.json", manifest_bytes)
    assert cid_manifest != cid_file, "Manifest CID should differ from content CID"
    _log_event(events_path, {"suite": "phase8_strict_fixed", "event": "ipfs_add_manifest", "cid": cid_manifest, "sha256": manifest_sha})

    # 5) FIXED: Use the actual storeContent mutation from the schema
    mutation = """
    mutation StoreContent($name:String!, $data:String!, $mimeType:String) {
      storeContent(name:$name, data:$data, mimeType:$mimeType) {
        id
        name
        encoding
        data
        witness {
          id
          proof
          verificationTime
          isValid
          conservationProof {
            pageConservation
            cycleConservation
            kleinProbes
            r96Classification {
              inputClass
              outputClass
              compressionRatio
              isValid
            }
          }
        }
        metadata {
          createdAt
          updatedAt
          size
          mimeType
          checksum
          atlas12288 {
            page
            cycle
            r96Class
            kleinWindow
            conservationHash
          }
        }
      }
    }
    """
    data = _gql(graphql_url, mutation, {
        "name": name,
        "data": content,
        "mimeType": "text/plain"
    })
    assert data and data.get("storeContent"), f"storeContent failed: {data}"
    stored_content = data["storeContent"]
    assert stored_content["name"] == name
    assert stored_content["data"] == content
    _log_event(events_path, {"suite": "phase8_strict_fixed", "event": "storeContent", "resp": stored_content})

    # 6) FIXED: Use the actual resolveContent query from the schema
    query = """
    query ResolveContent($name:String!) {
      resolveContent(name:$name) {
        id
        name
        encoding
        data
        witness {
          id
          proof
          verificationTime
          isValid
          conservationProof {
            pageConservation
            cycleConservation
            kleinProbes
            r96Classification {
              inputClass
              outputClass
              compressionRatio
              isValid
            }
          }
        }
        metadata {
          createdAt
          updatedAt
          size
          mimeType
          checksum
          atlas12288 {
            page
            cycle
            r96Class
            kleinWindow
            conservationHash
          }
        }
      }
    }
    """
    d2 = _gql(graphql_url, query, {"name": name})
    assert d2 and d2.get("resolveContent"), f"resolveContent returned no data: {d2}"
    res = d2["resolveContent"]

    # 7) Hard assertions: require proofs and non-empty encoding, data equality
    assert res.get("name") == name, "resolved name mismatch"
    assert res.get("data") == content, "resolved data should match stored content"
    enc = res.get("encoding")
    assert isinstance(enc, (str, bytes)) and len(enc) > 0, "encoding must be present and non-empty"
    
    # Check witness structure
    witness = res.get("witness")
    assert witness, "witness must be present"
    assert witness.get("isValid") is True, "witness must be valid"
    
    # Check conservation proof
    conservation_proof = witness.get("conservationProof")
    assert conservation_proof, "conservationProof must be present"
    assert conservation_proof.get("pageConservation") is True, "pageConservation must be true"
    assert conservation_proof.get("cycleConservation") is True, "cycleConservation must be true"
    
    # Check metadata
    metadata = res.get("metadata")
    assert metadata, "metadata must be present"
    assert metadata.get("size") == len(content), "metadata size should match content length"
    assert metadata.get("mimeType") == "text/plain", "metadata mimeType should match"

    # 8) Tamper-negative: flip one byte of manifest and verify CID changes
    tampered = bytearray(manifest_bytes)
    tampered[0] ^= 0x01
    cid_tampered = _ipfs_add(ipfs_api, "manifest.json", bytes(tampered))
    assert cid_tampered != cid_manifest, "Tampered manifest must produce a different CID"
    _log_event(events_path, {"suite": "phase8_strict_fixed", "event": "tamper_manifest", "original": cid_manifest, "tampered": cid_tampered})

    # 9) Idempotence: resolve again and confirm stability
    d3 = _gql(graphql_url, query, {"name": name})
    res2 = d3["resolveContent"]
    assert res2.get("data") == content, "data changed between resolves without an update"
    assert res2.get("encoding") == enc, "encoding changed between resolves unexpectedly"
    _log_event(events_path, {"suite": "phase8_strict_fixed", "event": "resolve_repeat", "data": res2.get("data")})

    # 10) Test resolution stats
    stats_query = """
    query {
      resolutionStats {
        totalContent
        totalResolutions
        averageResolutionTime
        conservationViolations
        bijectionIntegrity
      }
    }
    """
    stats_data = _gql(graphql_url, stats_query, {})
    assert stats_data and stats_data.get("resolutionStats"), "resolutionStats should be available"
    stats = stats_data["resolutionStats"]
    assert isinstance(stats.get("totalContent"), int), "totalContent should be an integer"
    assert isinstance(stats.get("bijectionIntegrity"), (int, float)), "bijectionIntegrity should be a number"
    _log_event(events_path, {"suite": "phase8_strict_fixed", "event": "resolution_stats", "stats": stats})

    # Done: if we got here, strict E2E guarantees are in place
    print("✅ Strict E2E test passed - all guarantees verified")

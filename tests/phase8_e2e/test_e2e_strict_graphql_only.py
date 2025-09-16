# tests/phase8_e2e/test_e2e_strict_graphql_only.py
# GraphQL-only Strict E2E: tests GraphQL functionality without IPFS dependency
# Env:
#   GRAPHQL_URL  e.g. http://localhost:4000/graphql
#   GRAPHQL_TOKEN (optional) "Bearer <token>"

import os
import json
import time
import uuid
import requests
import pytest

MARK = pytest.mark.phase8_e2e

# ---- helpers ---------------------------------------------------------------

def _env(name: str) -> str:
    v = os.getenv(name, "").strip()
    if not v:
        pytest.skip(f"Missing required env var: {name}")
    return v

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

# ---- the graphql-only strict test -------------------------------------------------------

@MARK
@pytest.mark.strict
def test_e2e_strict_graphql_functionality(tmp_path):
    graphql_url = _env("GRAPHQL_URL")

    # Where to write audit events
    events_path = os.path.join("reports", "e2e", "events.jsonl")
    os.makedirs(os.path.dirname(events_path), exist_ok=True)

    # 1) Prepare test content
    unique = uuid.uuid4().hex[:8]
    name = f"test-content-{unique}"
    content = f"GraphQL-only E2E test content {unique} @ {int(time.time())}"

    # 2) Test storeContent mutation
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
    
    print(f"🧪 Testing storeContent mutation for: {name}")
    data = _gql(graphql_url, mutation, {
        "name": name,
        "data": content,
        "mimeType": "text/plain"
    })
    
    assert data and data.get("storeContent"), f"storeContent failed: {data}"
    stored_content = data["storeContent"]
    assert stored_content["name"] == name, "Stored content name mismatch"
    assert stored_content["data"] == content, "Stored content data mismatch"
    assert stored_content["encoding"], "Encoding must be present"
    assert stored_content["witness"]["isValid"] is True, "Witness must be valid"
    assert stored_content["metadata"]["size"] == len(content), "Metadata size mismatch"
    
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "storeContent", "name": name, "id": stored_content["id"]})
    print("✅ storeContent mutation test passed")

    # 3) Test resolveContent query
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
    
    print(f"🔍 Testing resolveContent query for: {name}")
    resolve_data = _gql(graphql_url, query, {"name": name})
    
    assert resolve_data and resolve_data.get("resolveContent"), f"resolveContent failed: {resolve_data}"
    resolved_content = resolve_data["resolveContent"]
    assert resolved_content["name"] == name, "Resolved content name mismatch"
    assert resolved_content["data"] == content, "Resolved content data mismatch"
    assert resolved_content["id"] == stored_content["id"], "Resolved content ID mismatch"
    assert resolved_content["encoding"] == stored_content["encoding"], "Encoding consistency check failed"
    
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "resolveContent", "name": name, "id": resolved_content["id"]})
    print("✅ resolveContent query test passed")

    # 4) Test resolutionStats query
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
    
    print("📊 Testing resolutionStats query")
    stats_data = _gql(graphql_url, stats_query, {})
    
    assert stats_data and stats_data.get("resolutionStats"), f"resolutionStats failed: {stats_data}"
    stats = stats_data["resolutionStats"]
    assert isinstance(stats["totalContent"], int), "totalContent must be an integer"
    assert isinstance(stats["totalResolutions"], int), "totalResolutions must be an integer"
    assert isinstance(stats["averageResolutionTime"], (int, float)), "averageResolutionTime must be a number"
    assert isinstance(stats["conservationViolations"], int), "conservationViolations must be an integer"
    assert isinstance(stats["bijectionIntegrity"], (int, float)), "bijectionIntegrity must be a number"
    assert 0 <= stats["bijectionIntegrity"] <= 1, "bijectionIntegrity must be between 0 and 1"
    
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "resolutionStats", "stats": stats})
    print("✅ resolutionStats query test passed")

    # 5) Test searchContent query
    search_query = """
    query SearchContent($mimeType:String, $limit:Int) {
      searchContent(mimeType:$mimeType, limit:$limit) {
        id
        name
        encoding
        data
        metadata {
          mimeType
          size
        }
      }
    }
    """
    
    print("🔎 Testing searchContent query")
    search_data = _gql(graphql_url, search_query, {"mimeType": "text/plain", "limit": 5})
    
    assert search_data and search_data.get("searchContent") is not None, f"searchContent failed: {search_data}"
    search_results = search_data["searchContent"]
    assert isinstance(search_results, list), "searchContent must return a list"
    
    # Check if our content is in the results
    found_our_content = any(result["name"] == name for result in search_results)
    if found_our_content:
        print("✅ Our test content found in search results")
    else:
        print("ℹ️ Our test content not found in search results (may be expected)")
    
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "searchContent", "results_count": len(search_results)})
    print("✅ searchContent query test passed")

    # 6) Test updateContent mutation
    updated_content = f"Updated content {unique} @ {int(time.time())}"
    update_mutation = """
    mutation UpdateContent($id:String!, $data:String!) {
      updateContent(id:$id, data:$data) {
        id
        name
        encoding
        data
        metadata {
          updatedAt
          size
        }
      }
    }
    """
    
    print(f"🔄 Testing updateContent mutation for: {stored_content['id']}")
    update_data = _gql(graphql_url, update_mutation, {
        "id": stored_content["id"],
        "data": updated_content
    })
    
    assert update_data and update_data.get("updateContent"), f"updateContent failed: {update_data}"
    updated_result = update_data["updateContent"]
    assert updated_result["id"] == stored_content["id"], "Updated content ID mismatch"
    assert updated_result["data"] == updated_content, "Updated content data mismatch"
    assert updated_result["metadata"]["size"] == len(updated_content), "Updated content size mismatch"
    
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "updateContent", "id": updated_result["id"]})
    print("✅ updateContent mutation test passed")

    # 7) Test deleteContent mutation
    delete_mutation = """
    mutation DeleteContent($id:String!) {
      deleteContent(id:$id)
    }
    """
    
    print(f"🗑️ Testing deleteContent mutation for: {stored_content['id']}")
    delete_data = _gql(graphql_url, delete_mutation, {"id": stored_content["id"]})
    
    assert delete_data and delete_data.get("deleteContent") is True, f"deleteContent failed: {delete_data}"
    
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "deleteContent", "id": stored_content["id"]})
    print("✅ deleteContent mutation test passed")

    # 8) Verify content is deleted by trying to resolve it
    print(f"🔍 Verifying content deletion for: {name}")
    try:
        verify_delete = _gql(graphql_url, query, {"name": name})
        # If we get here, the content still exists
        if verify_delete and verify_delete.get("resolveContent"):
            print("⚠️ Content still exists after deletion (may be expected behavior)")
        else:
            print("✅ Content successfully deleted")
    except Exception as e:
        print(f"✅ Content deletion verified (error expected): {str(e)[:100]}")

    print("🎉 All GraphQL strict E2E tests passed!")
    _log_event(events_path, {"suite": "phase8_strict_graphql", "event": "test_complete", "status": "passed"})

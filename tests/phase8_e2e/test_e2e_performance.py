# tests/phase8_e2e/test_e2e_performance.py
# Performance-validated E2E: combines strict E2E with load generation
# Env:
#   IPFS_API     e.g. http://127.0.0.1:5001
#   GRAPHQL_URL  e.g. http://localhost:4000/graphql
#   GRAPHQL_TOKEN (optional) "Bearer <token>"
#   E2E_PERF_DURATION (optional) e.g. 10 (seconds)
#   E2E_PERF_LANES (optional) e.g. 8
#   E2E_PERF_PAYLOAD (optional) e.g. 4096 (bytes)

import os
import io
import json
import time
import uuid
import hashlib
import requests
import pytest
import asyncio
import subprocess
import tempfile
from pathlib import Path

MARK = pytest.mark.phase8_e2e

# ---- helpers ---------------------------------------------------------------

def _env(name: str, default: str = "") -> str:
    v = os.getenv(name, default).strip()
    if not v and not default:
        pytest.skip(f"Missing required env var: {name}")
    return v

def _sha256_hex(b: bytes) -> str:
    h = hashlib.sha256()
    h.update(b)
    return h.hexdigest()

def _ipfs_add(ipfs_api: str, filename: str, data: bytes) -> str:
    url = f"{ipfs_api.rstrip('/')}/api/v0/add"
    files = {'file': (filename, io.BytesIO(data))}
    r = requests.post(url, params={"pin": "true"}, files=files, timeout=30)
    r.raise_for_status()
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

def _run_load_generator(duration_sec: int, lanes: int, payload_bytes: int, target_gbps: float) -> dict:
    """Run the TypeScript load generator and return performance stats"""
    
    # Create a temporary config file for the load generator
    config = {
        "durationSec": duration_sec,
        "lanes": lanes,
        "payloadBytes": payload_bytes,
        "targetGbps": target_gbps,
        "batch": 8,
        "windowMs": 100,
        "workers": 4,
        "budget": {
            "io": 1000,
            "cpuMs": 100
        }
    }
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        json.dump(config, f)
        config_path = f.name
    
    try:
        # Run the load generator using Node.js
        cmd = [
            "node", 
            "-e", 
            f"""
            const {{ runLoad }} = require('./apps/HoloPost/src/bench/loadgen.ts');
            const config = require('{config_path}');
            
            runLoad(config).then(stats => {{
                console.log(JSON.stringify(stats));
            }}).catch(err => {{
                console.error('Load generator error:', err);
                process.exit(1);
            }});
            """
        ]
        
        result = subprocess.run(
            cmd, 
            capture_output=True, 
            text=True, 
            timeout=duration_sec + 30,  # Add buffer for startup/cleanup
            cwd=os.getcwd()
        )
        
        if result.returncode != 0:
            raise RuntimeError(f"Load generator failed: {result.stderr}")
        
        # Parse the JSON output
        stats = json.loads(result.stdout.strip())
        return stats
        
    finally:
        # Clean up temp file
        try:
            os.unlink(config_path)
        except:
            pass

# ---- the performance E2E test ----------------------------------------------

@MARK
@pytest.mark.performance
def test_e2e_performance_publish_register_resolve_verify_with_load(tmp_path):
    """E2E test that validates both correctness AND performance under load"""
    
    ipfs_api = _env("IPFS_API")
    graphql_url = _env("GRAPHQL_URL")
    
    # Performance test parameters
    duration_sec = int(_env("E2E_PERF_DURATION", "5"))
    lanes = int(_env("E2E_PERF_LANES", "8"))
    payload_bytes = int(_env("E2E_PERF_PAYLOAD", "4096"))
    target_gbps = float(_env("E2E_PERF_TARGET_GBPS", "1.0"))
    
    # Where to write audit events
    events_path = os.path.join("reports", "e2e", "performance_events.jsonl")
    os.makedirs(os.path.dirname(events_path), exist_ok=True)
    
    print(f"🚀 Starting performance E2E test: {duration_sec}s, {lanes} lanes, {payload_bytes}B, {target_gbps} Gb/s")
    
    # 1) Prepare test content
    unique = uuid.uuid4().hex[:8]
    name = f"perf/docs/strict-{unique}"
    content = f"Performance E2E demo {unique} @ {int(time.time())}\n".encode("utf-8")
    content_sha = _sha256_hex(content)
    
    # 2) Upload to IPFS
    cid_file = _ipfs_add(ipfs_api, "demo.txt", content)
    _log_event(events_path, {
        "suite": "phase8_performance", 
        "event": "ipfs_add_file", 
        "cid": cid_file, 
        "sha256": content_sha
    })
    
    # 3) Create manifest
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
    
    # 4) Upload manifest to IPFS
    cid_manifest = _ipfs_add(ipfs_api, "manifest.json", manifest_bytes)
    assert cid_manifest != cid_file, "Manifest CID should differ from content CID"
    _log_event(events_path, {
        "suite": "phase8_performance", 
        "event": "ipfs_add_manifest", 
        "cid": cid_manifest, 
        "sha256": manifest_sha
    })
    
    # 5) Register in GraphQL
    mutation = """
    mutation Publish($name:String!, $cid:String!, $manifestCid:String!, $sha256:String!) {
      publishApp(name:$name, cid:$cid, manifestCid:$manifestCid, sha256:$sha256) {
        ok
        name
        cid
        manifestCid
      }
    }
    """
    data = _gql(graphql_url, mutation, {
        "name": name,
        "cid": cid_file,
        "manifestCid": cid_manifest,
        "sha256": manifest_sha
    })
    assert data and data.get("publishApp") and data["publishApp"].get("ok") is True, f"publishApp failed: {data}"
    assert data["publishApp"]["name"] == name
    assert data["publishApp"]["cid"] == cid_file
    _log_event(events_path, {
        "suite": "phase8_performance", 
        "event": "publishApp", 
        "resp": data["publishApp"]
    })
    
    # 6) Verify resolve works
    query = """
    query Resolve($name:String!) {
      resolve(name:$name) {
        name
        cid
        manifestCid
        encoding
        proofs {
          merkleRoot
          witnesses
        }
      }
    }
    """
    d2 = _gql(graphql_url, query, {"name": name})
    assert d2 and d2.get("resolve"), f"resolve returned no data: {d2}"
    res = d2["resolve"]
    
    # Validate resolve response
    assert res.get("name") == name, "resolved name mismatch"
    assert res.get("cid") == cid_file, "resolved CID should match published file CID"
    enc = res.get("encoding")
    assert isinstance(enc, (str, bytes)) and len(enc) > 0, "encoding must be present and non-empty"
    proofs = res.get("proofs") or {}
    assert proofs.get("merkleRoot"), "proofs.merkleRoot must be present"
    witnesses = proofs.get("witnesses")
    assert witnesses and (isinstance(witnesses, (list, str)) or isinstance(witnesses, dict)), "proofs.witnesses must be present (non-empty)"
    
    _log_event(events_path, {
        "suite": "phase8_performance", 
        "event": "resolve_validation", 
        "encoding_len": len(enc) if isinstance(enc, (str, bytes)) else 0,
        "has_proofs": bool(proofs.get("merkleRoot"))
    })
    
    # 7) NOW RUN LOAD GENERATOR TO TEST PERFORMANCE UNDER LOAD
    print(f"🔥 Starting load generator: {duration_sec}s, {lanes} lanes, {payload_bytes}B, {target_gbps} Gb/s")
    
    try:
        load_stats = _run_load_generator(duration_sec, lanes, payload_bytes, target_gbps)
        
        _log_event(events_path, {
            "suite": "phase8_performance", 
            "event": "load_generator_complete", 
            "stats": load_stats
        })
        
        # Validate performance metrics
        print(f"📊 Load generator results:")
        print(f"   Throughput: {load_stats.get('gbps', 0):.2f} Gb/s (target: {target_gbps})")
        print(f"   Frames/sec: {load_stats.get('fps', 0):.0f}")
        print(f"   Sent: {load_stats.get('sent', 0)}")
        print(f"   Delivered: {load_stats.get('delivered', 0)}")
        print(f"   Rejected: {load_stats.get('rejected', 0)}")
        print(f"   P50 Latency: {load_stats.get('p50latencyMs', 0):.2f}ms")
        print(f"   P99 Latency: {load_stats.get('p99latencyMs', 0):.2f}ms")
        print(f"   CPU Usage: {load_stats.get('cpuPercent', 0):.1f}%")
        
        # Performance assertions
        delivered = load_stats.get('delivered', 0)
        sent = load_stats.get('sent', 0)
        
        # At least 80% of sent frames should be delivered
        if sent > 0:
            delivery_rate = delivered / sent
            assert delivery_rate >= 0.8, f"Delivery rate {delivery_rate:.2%} below 80% threshold"
            print(f"✅ Delivery rate: {delivery_rate:.2%}")
        
        # Throughput should be reasonable (at least 50% of target)
        achieved_gbps = load_stats.get('gbps', 0)
        if target_gbps > 0:
            throughput_ratio = achieved_gbps / target_gbps
            assert throughput_ratio >= 0.5, f"Throughput {achieved_gbps:.2f} Gb/s below 50% of target {target_gbps}"
            print(f"✅ Throughput ratio: {throughput_ratio:.2%}")
        
        # Latency should be reasonable (P99 under 100ms for this test)
        p99_latency = load_stats.get('p99latencyMs', 0)
        assert p99_latency < 100, f"P99 latency {p99_latency:.2f}ms exceeds 100ms threshold"
        print(f"✅ P99 latency: {p99_latency:.2f}ms")
        
        # CPU usage should be reasonable (under 80% for this test)
        cpu_percent = load_stats.get('cpuPercent', 0)
        assert cpu_percent < 80, f"CPU usage {cpu_percent:.1f}% exceeds 80% threshold"
        print(f"✅ CPU usage: {cpu_percent:.1f}%")
        
    except Exception as e:
        _log_event(events_path, {
            "suite": "phase8_performance", 
            "event": "load_generator_error", 
            "error": str(e)
        })
        pytest.fail(f"Load generator failed: {e}")
    
    # 8) Verify system still works after load test
    print("🔄 Verifying system stability after load test...")
    
    # Resolve again to ensure system is still responsive
    d3 = _gql(graphql_url, query, {"name": name})
    res2 = d3["resolve"]
    assert res2.get("cid") == cid_file, "CID changed after load test"
    assert res2.get("encoding") == enc, "encoding changed after load test"
    
    _log_event(events_path, {
        "suite": "phase8_performance", 
        "event": "post_load_validation", 
        "cid_stable": res2.get("cid") == cid_file,
        "encoding_stable": res2.get("encoding") == enc
    })
    
    print("✅ Performance E2E test completed successfully!")
    print(f"   - E2E correctness: ✅")
    print(f"   - Performance under load: ✅")
    print(f"   - System stability: ✅")

@MARK
@pytest.mark.performance
def test_e2e_performance_stress_test():
    """Stress test with higher load to find breaking points"""
    
    ipfs_api = _env("IPFS_API")
    graphql_url = _env("GRAPHQL_URL")
    
    # Stress test parameters (higher load)
    duration_sec = int(_env("E2E_STRESS_DURATION", "10"))
    lanes = int(_env("E2E_STRESS_LANES", "32"))
    payload_bytes = int(_env("E2E_STRESS_PAYLOAD", "8192"))
    target_gbps = float(_env("E2E_STRESS_TARGET_GBPS", "5.0"))
    
    events_path = os.path.join("reports", "e2e", "stress_events.jsonl")
    os.makedirs(os.path.dirname(events_path), exist_ok=True)
    
    print(f"💥 Starting stress test: {duration_sec}s, {lanes} lanes, {payload_bytes}B, {target_gbps} Gb/s")
    
    try:
        load_stats = _run_load_generator(duration_sec, lanes, payload_bytes, target_gbps)
        
        _log_event(events_path, {
            "suite": "phase8_stress", 
            "event": "stress_test_complete", 
            "stats": load_stats
        })
        
        # Stress test has more lenient thresholds
        delivered = load_stats.get('delivered', 0)
        sent = load_stats.get('sent', 0)
        
        if sent > 0:
            delivery_rate = delivered / sent
            # Stress test: at least 60% delivery rate
            assert delivery_rate >= 0.6, f"Stress test delivery rate {delivery_rate:.2%} below 60% threshold"
            print(f"✅ Stress delivery rate: {delivery_rate:.2%}")
        
        # Stress test: at least 30% of target throughput
        achieved_gbps = load_stats.get('gbps', 0)
        if target_gbps > 0:
            throughput_ratio = achieved_gbps / target_gbps
            assert throughput_ratio >= 0.3, f"Stress throughput {achieved_gbps:.2f} Gb/s below 30% of target {target_gbps}"
            print(f"✅ Stress throughput ratio: {throughput_ratio:.2%}")
        
        print("✅ Stress test completed successfully!")
        
    except Exception as e:
        _log_event(events_path, {
            "suite": "phase8_stress", 
            "event": "stress_test_error", 
            "error": str(e)
        })
        pytest.fail(f"Stress test failed: {e}")

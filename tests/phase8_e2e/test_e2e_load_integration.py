# tests/phase8_e2e/test_e2e_load_integration.py
# E2E test with integrated load generation (Python-based)
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
import asyncio
import concurrent.futures
from typing import Dict, List, Any

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

# ---- Python-based load generator -------------------------------------------

class LoadGenerator:
    """Python-based load generator for E2E testing"""
    
    def __init__(self, graphql_url: str, ipfs_api: str):
        self.graphql_url = graphql_url
        self.ipfs_api = ipfs_api
        self.stats = {
            'sent': 0,
            'delivered': 0,
            'rejected': 0,
            'latencies': [],
            'errors': []
        }
    
    def _create_test_content(self, size: int) -> bytes:
        """Create deterministic test content"""
        return bytes([i % 256 for i in range(size)])
    
    def _publish_content(self, name: str, content: bytes) -> str:
        """Publish content to IPFS and register in GraphQL"""
        # Upload to IPFS
        cid_file = _ipfs_add(self.ipfs_api, f"{name}.bin", content)
        content_sha = _sha256_hex(content)
        
        # Create manifest
        manifest_obj = {
            "name": name,
            "kind": "document",
            "mime": "application/octet-stream",
            "size": len(content),
            "sha256": content_sha,
            "cid": cid_file,
            "version": 1,
            "ts": int(time.time())
        }
        manifest_bytes = json.dumps(manifest_obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
        manifest_sha = _sha256_hex(manifest_bytes)
        
        # Upload manifest
        cid_manifest = _ipfs_add(self.ipfs_api, f"{name}-manifest.json", manifest_bytes)
        
        # Register in GraphQL
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
        data = _gql(self.graphql_url, mutation, {
            "name": name,
            "cid": cid_file,
            "manifestCid": cid_manifest,
            "sha256": manifest_sha
        })
        
        if not (data and data.get("publishApp") and data["publishApp"].get("ok")):
            raise RuntimeError(f"Failed to publish: {data}")
        
        return name
    
    def _resolve_content(self, name: str) -> dict:
        """Resolve content by name"""
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
        return _gql(self.graphql_url, query, {"name": name})
    
    def _worker(self, worker_id: int, num_operations: int, payload_size: int) -> dict:
        """Worker function for load generation"""
        worker_stats = {
            'sent': 0,
            'delivered': 0,
            'rejected': 0,
            'latencies': [],
            'errors': []
        }
        
        for i in range(num_operations):
            try:
                start_time = time.time()
                
                # Create unique content
                unique_id = f"worker-{worker_id}-op-{i}-{uuid.uuid4().hex[:8]}"
                name = f"load-test/{unique_id}"
                content = self._create_test_content(payload_size)
                
                # Publish
                published_name = self._publish_content(name, content)
                worker_stats['sent'] += 1
                
                # Resolve
                result = self._resolve_content(published_name)
                if result and result.get("resolve"):
                    worker_stats['delivered'] += 1
                else:
                    worker_stats['rejected'] += 1
                    worker_stats['errors'].append(f"Resolve failed for {published_name}")
                
                # Record latency
                latency = (time.time() - start_time) * 1000  # Convert to ms
                worker_stats['latencies'].append(latency)
                
            except Exception as e:
                worker_stats['rejected'] += 1
                worker_stats['errors'].append(str(e))
        
        return worker_stats
    
    def run_load_test(self, duration_sec: int, num_workers: int, payload_size: int, ops_per_second: int) -> dict:
        """Run load test with multiple workers"""
        print(f"🚀 Starting load test: {duration_sec}s, {num_workers} workers, {payload_size}B payload, {ops_per_second} ops/s")
        
        # Calculate operations per worker
        total_ops = duration_sec * ops_per_second
        ops_per_worker = max(1, total_ops // num_workers)
        
        start_time = time.time()
        
        # Run workers in parallel
        with concurrent.futures.ThreadPoolExecutor(max_workers=num_workers) as executor:
            futures = []
            for worker_id in range(num_workers):
                future = executor.submit(self._worker, worker_id, ops_per_worker, payload_size)
                futures.append(future)
            
            # Collect results
            worker_results = []
            for future in concurrent.futures.as_completed(futures):
                try:
                    result = future.result()
                    worker_results.append(result)
                except Exception as e:
                    print(f"Worker failed: {e}")
                    worker_results.append({
                        'sent': 0, 'delivered': 0, 'rejected': 1,
                        'latencies': [], 'errors': [str(e)]
                    })
        
        end_time = time.time()
        actual_duration = end_time - start_time
        
        # Aggregate results
        total_sent = sum(r['sent'] for r in worker_results)
        total_delivered = sum(r['delivered'] for r in worker_results)
        total_rejected = sum(r['rejected'] for r in worker_results)
        all_latencies = []
        all_errors = []
        
        for result in worker_results:
            all_latencies.extend(result['latencies'])
            all_errors.extend(result['errors'])
        
        # Calculate statistics
        if all_latencies:
            all_latencies.sort()
            p50 = all_latencies[len(all_latencies) // 2]
            p99 = all_latencies[int(len(all_latencies) * 0.99)]
            avg_latency = sum(all_latencies) / len(all_latencies)
        else:
            p50 = p99 = avg_latency = 0
        
        # Calculate throughput
        actual_ops_per_sec = total_delivered / actual_duration if actual_duration > 0 else 0
        throughput_mbps = (total_delivered * payload_size * 8) / (actual_duration * 1e6) if actual_duration > 0 else 0
        
        return {
            'duration_sec': actual_duration,
            'sent': total_sent,
            'delivered': total_delivered,
            'rejected': total_rejected,
            'ops_per_sec': actual_ops_per_sec,
            'throughput_mbps': throughput_mbps,
            'p50_latency_ms': p50,
            'p99_latency_ms': p99,
            'avg_latency_ms': avg_latency,
            'error_count': len(all_errors),
            'errors': all_errors[:10]  # First 10 errors for debugging
        }

# ---- the integrated E2E + load test ----------------------------------------

@MARK
@pytest.mark.performance
def test_e2e_with_load_generation():
    """E2E test that validates correctness AND performance under load"""
    
    ipfs_api = _env("IPFS_API")
    graphql_url = _env("GRAPHQL_URL")
    
    # Test parameters
    duration_sec = int(_env("E2E_LOAD_DURATION", "5"))
    num_workers = int(_env("E2E_LOAD_WORKERS", "4"))
    payload_size = int(_env("E2E_LOAD_PAYLOAD", "1024"))
    ops_per_second = int(_env("E2E_LOAD_OPS_PER_SEC", "10"))
    
    events_path = os.path.join("reports", "e2e", "load_events.jsonl")
    os.makedirs(os.path.dirname(events_path), exist_ok=True)
    
    print(f"🚀 Starting E2E + Load test: {duration_sec}s, {num_workers} workers, {payload_size}B, {ops_per_second} ops/s")
    
    # Initialize load generator
    load_gen = LoadGenerator(graphql_url, ipfs_api)
    
    # Run load test
    start_time = time.time()
    stats = load_gen.run_load_test(duration_sec, num_workers, payload_size, ops_per_second)
    end_time = time.time()
    
    _log_event(events_path, {
        "suite": "phase8_load", 
        "event": "load_test_complete", 
        "stats": stats
    })
    
    # Print results
    print(f"📊 Load test results:")
    print(f"   Duration: {stats['duration_sec']:.2f}s")
    print(f"   Sent: {stats['sent']}")
    print(f"   Delivered: {stats['delivered']}")
    print(f"   Rejected: {stats['rejected']}")
    print(f"   Ops/sec: {stats['ops_per_sec']:.2f}")
    print(f"   Throughput: {stats['throughput_mbps']:.2f} Mbps")
    print(f"   P50 Latency: {stats['p50_latency_ms']:.2f}ms")
    print(f"   P99 Latency: {stats['p99_latency_ms']:.2f}ms")
    print(f"   Avg Latency: {stats['avg_latency_ms']:.2f}ms")
    print(f"   Errors: {stats['error_count']}")
    
    # Performance assertions
    sent = stats['sent']
    delivered = stats['delivered']
    
    # At least 80% of sent operations should be delivered
    if sent > 0:
        delivery_rate = delivered / sent
        assert delivery_rate >= 0.8, f"Delivery rate {delivery_rate:.2%} below 80% threshold"
        print(f"✅ Delivery rate: {delivery_rate:.2%}")
    
    # Should achieve reasonable throughput
    assert stats['throughput_mbps'] > 0.1, f"Throughput {stats['throughput_mbps']:.2f} Mbps too low"
    print(f"✅ Throughput: {stats['throughput_mbps']:.2f} Mbps")
    
    # Latency should be reasonable
    assert stats['p99_latency_ms'] < 5000, f"P99 latency {stats['p99_latency_ms']:.2f}ms too high"
    print(f"✅ P99 latency: {stats['p99_latency_ms']:.2f}ms")
    
    # Error rate should be low
    error_rate = stats['error_count'] / max(1, sent)
    assert error_rate < 0.1, f"Error rate {error_rate:.2%} too high"
    print(f"✅ Error rate: {error_rate:.2%}")
    
    print("✅ E2E + Load test completed successfully!")

@MARK
@pytest.mark.performance
def test_e2e_stress_test():
    """Stress test with higher load"""
    
    ipfs_api = _env("IPFS_API")
    graphql_url = _env("GRAPHQL_URL")
    
    # Stress test parameters
    duration_sec = int(_env("E2E_STRESS_DURATION", "10"))
    num_workers = int(_env("E2E_STRESS_WORKERS", "8"))
    payload_size = int(_env("E2E_STRESS_PAYLOAD", "4096"))
    ops_per_second = int(_env("E2E_STRESS_OPS_PER_SEC", "20"))
    
    events_path = os.path.join("reports", "e2e", "stress_events.jsonl")
    os.makedirs(os.path.dirname(events_path), exist_ok=True)
    
    print(f"💥 Starting stress test: {duration_sec}s, {num_workers} workers, {payload_size}B, {ops_per_second} ops/s")
    
    load_gen = LoadGenerator(graphql_url, ipfs_api)
    
    try:
        stats = load_gen.run_load_test(duration_sec, num_workers, payload_size, ops_per_second)
        
        _log_event(events_path, {
            "suite": "phase8_stress", 
            "event": "stress_test_complete", 
            "stats": stats
        })
        
        # Stress test has more lenient thresholds
        sent = stats['sent']
        delivered = stats['delivered']
        
        if sent > 0:
            delivery_rate = delivered / sent
            # Stress test: at least 60% delivery rate
            assert delivery_rate >= 0.6, f"Stress delivery rate {delivery_rate:.2%} below 60% threshold"
            print(f"✅ Stress delivery rate: {delivery_rate:.2%}")
        
        # Should achieve some throughput
        assert stats['throughput_mbps'] > 0.05, f"Stress throughput {stats['throughput_mbps']:.2f} Mbps too low"
        print(f"✅ Stress throughput: {stats['throughput_mbps']:.2f} Mbps")
        
        print("✅ Stress test completed successfully!")
        
    except Exception as e:
        _log_event(events_path, {
            "suite": "phase8_stress", 
            "event": "stress_test_error", 
            "error": str(e)
        })
        pytest.fail(f"Stress test failed: {e}")

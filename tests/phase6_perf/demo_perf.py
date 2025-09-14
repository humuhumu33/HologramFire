#!/usr/bin/env python3
"""
Demo script showing Phase 6 performance testing in action.
Run this to see how the performance utilities work.
"""

import time
import random
from _perf_utils import measure, write_csv

def mock_encode(data):
    """Simulate an encode operation with some variability"""
    # Simulate processing time based on data size
    base_time = len(data) / 1000000  # 1ms per MB
    jitter = random.uniform(0.5, 1.5)  # ±50% variability
    time.sleep(base_time * jitter)
    return f"encoded_{len(data)}_bytes"

def mock_verify(state):
    """Simulate a verify operation"""
    # Simulate verification time
    time.sleep(random.uniform(0.005, 0.015))  # 5-15ms
    return True

def demo_performance_testing():
    print("🚀 Phase 6 Performance Testing Demo")
    print("=" * 50)
    
    # Test encode performance
    print("\n📊 Testing encode performance...")
    test_data = b"x" * (1024 * 1024)  # 1MB
    encode_stats = measure(mock_encode, test_data, warmup=3, runs=10)
    
    print(f"  Encode p50: {encode_stats['p50']:.2f}ms")
    print(f"  Encode p95: {encode_stats['p95']:.2f}ms")
    print(f"  Encode p99: {encode_stats['p99']:.2f}ms")
    print(f"  Encode avg: {encode_stats['avg']:.2f}ms")
    
    # Test verify performance
    print("\n🔍 Testing verify performance...")
    test_state = {"data": "test_state"}
    verify_stats = measure(mock_verify, test_state, warmup=5, runs=15)
    
    print(f"  Verify p50: {verify_stats['p50']:.2f}ms")
    print(f"  Verify p95: {verify_stats['p95']:.2f}ms")
    print(f"  Verify p99: {verify_stats['p99']:.2f}ms")
    print(f"  Verify avg: {verify_stats['avg']:.2f}ms")
    
    # Write CSV artifacts
    print("\n📝 Writing CSV artifacts...")
    csv_path = write_csv([
        ["demo", "encode_1MB_ms", f"{encode_stats['p50']:.3f}", f"{encode_stats['p95']:.3f}",
         f"{encode_stats['p99']:.3f}", f"{encode_stats['avg']:.3f}", encode_stats["n"], "demo.encode"],
        ["demo", "verify_ms", f"{verify_stats['p50']:.3f}", f"{verify_stats['p95']:.3f}",
         f"{verify_stats['p99']:.3f}", f"{verify_stats['avg']:.3f}", verify_stats["n"], "demo.verify"]
    ], "demo_perf.csv")
    
    print(f"  CSV written to: {csv_path}")
    
    # Check SLOs
    print("\n🎯 SLO Check:")
    encode_slo = 100  # ms
    verify_slo = 10   # ms
    
    encode_pass = encode_stats['p95'] < encode_slo
    verify_pass = verify_stats['p95'] < verify_slo
    
    print(f"  Encode p95 < {encode_slo}ms: {'✅ PASS' if encode_pass else '❌ FAIL'} ({encode_stats['p95']:.2f}ms)")
    print(f"  Verify p95 < {verify_slo}ms: {'✅ PASS' if verify_pass else '❌ FAIL'} ({verify_stats['p95']:.2f}ms)")
    
    if encode_pass and verify_pass:
        print("\n🎉 All SLOs passed!")
    else:
        print("\n⚠️  Some SLOs failed - consider optimization or threshold adjustment")
    
    print(f"\n📁 Check reports/perf/ for CSV artifacts")

if __name__ == "__main__":
    demo_performance_testing()

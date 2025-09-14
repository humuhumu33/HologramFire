#!/usr/bin/env python3
"""
Cache profiling utility for performance tests.
Tracks cold vs warm cache performance.
"""
import time
import json
import os
from pathlib import Path
from typing import Dict, Any, Optional

CACHE_PROFILE_FILE = Path("reports/perf/cache_profiles.json")

class CacheProfiler:
    """Profiles cold vs warm cache performance."""
    
    def __init__(self):
        self.profiles: Dict[str, Dict[str, Any]] = {}
        self.current_test: Optional[str] = None
        self.start_time: Optional[float] = None
    
    def start_test(self, test_name: str, cache_type: str = "cold"):
        """Start profiling a test."""
        self.current_test = f"{test_name}_{cache_type}"
        self.start_time = time.time()
        print(f"🔥 Starting {cache_type} cache test: {test_name}")
    
    def end_test(self, test_name: str, cache_type: str = "cold", **metrics):
        """End profiling a test and record metrics."""
        if not self.start_time:
            return
        
        duration = time.time() - self.start_time
        test_key = f"{test_name}_{cache_type}"
        
        if test_key not in self.profiles:
            self.profiles[test_key] = {}
        
        self.profiles[test_key].update({
            "test_name": test_name,
            "cache_type": cache_type,
            "duration_ms": duration * 1000,
            "timestamp": time.time(),
            **metrics
        })
        
        print(f"✅ {cache_type} cache test completed: {test_name} ({duration*1000:.1f}ms)")
        self.start_time = None
    
    def save_profiles(self):
        """Save cache profiles to file."""
        CACHE_PROFILE_FILE.parent.mkdir(parents=True, exist_ok=True)
        
        # Load existing profiles
        existing = {}
        if CACHE_PROFILE_FILE.exists():
            try:
                with CACHE_PROFILE_FILE.open("r") as f:
                    existing = json.load(f)
            except:
                pass
        
        # Merge with new profiles
        existing.update(self.profiles)
        
        # Save back
        with CACHE_PROFILE_FILE.open("w") as f:
            json.dump(existing, f, indent=2)
        
        print(f"💾 Saved cache profiles to {CACHE_PROFILE_FILE}")
    
    def get_cache_ratio(self, test_name: str) -> Optional[float]:
        """Get cold/warm cache performance ratio."""
        cold_key = f"{test_name}_cold"
        warm_key = f"{test_name}_warm"
        
        if cold_key not in self.profiles or warm_key not in self.profiles:
            return None
        
        cold_duration = self.profiles[cold_key]["duration_ms"]
        warm_duration = self.profiles[warm_key]["duration_ms"]
        
        return cold_duration / warm_duration if warm_duration > 0 else None

# Global profiler instance
profiler = CacheProfiler()

def profile_cache(test_name: str, cache_type: str = "cold"):
    """Decorator for profiling cache performance."""
    def decorator(func):
        def wrapper(*args, **kwargs):
            profiler.start_test(test_name, cache_type)
            try:
                result = func(*args, **kwargs)
                profiler.end_test(test_name, cache_type)
                return result
            except Exception as e:
                profiler.end_test(test_name, cache_type, error=str(e))
                raise
        return wrapper
    return decorator

def run_cold_warm_test(test_name: str, test_func, *args, **kwargs):
    """Run a test twice (cold then warm) and profile both."""
    # Cold run
    profiler.start_test(test_name, "cold")
    try:
        result1 = test_func(*args, **kwargs)
        profiler.end_test(test_name, "cold")
    except Exception as e:
        profiler.end_test(test_name, "cold", error=str(e))
        raise
    
    # Warm run
    profiler.start_test(test_name, "warm")
    try:
        result2 = test_func(*args, **kwargs)
        profiler.end_test(test_name, "warm")
    except Exception as e:
        profiler.end_test(test_name, "warm", error=str(e))
        raise
    
    # Calculate ratio
    ratio = profiler.get_cache_ratio(test_name)
    if ratio:
        print(f"📊 Cache ratio for {test_name}: {ratio:.2f}x (cold/warm)")
    
    return result1, result2

if __name__ == "__main__":
    # Example usage
    def sample_test():
        time.sleep(0.1)  # Simulate work
        return "done"
    
    # Test the profiler
    run_cold_warm_test("sample", sample_test)
    profiler.save_profiles()

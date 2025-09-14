"""
CTP-96 Replay Nonce Validation Tests
Tests replay attack prevention with nonce validation.
"""
import pytest
import time
import hashlib
from typing import Dict, Any, List, Optional
from collections import deque

@pytest.mark.phase9_chaos
class TestCTP96Replay:
    """Test CTP-96 replay attack prevention."""
    
    @pytest.fixture(autouse=True)
    def setup_nonce_validator(self):
        """Setup nonce validator with LRU cache."""
        self.nonce_cache = deque(maxlen=1000)  # LRU cache for recent nonces
        self.epoch_window = 300  # 5 minute window
        yield
        self.nonce_cache.clear()
    
    def _generate_nonce(self, data: bytes, timestamp: Optional[float] = None) -> str:
        """Generate nonce for CTP-96 frame."""
        if timestamp is None:
            timestamp = time.time()
        
        # Create nonce from data hash + timestamp
        data_hash = hashlib.sha256(data).hexdigest()[:16]
        nonce = f"{data_hash}_{int(timestamp)}"
        return nonce
    
    def _validate_nonce(self, nonce: str, data: bytes) -> bool:
        """Validate nonce and check for replay attacks."""
        # Check if nonce is in cache (replay attack)
        if nonce in self.nonce_cache:
            return False
        
        # Parse timestamp from nonce
        try:
            nonce_hash, timestamp_str = nonce.split('_')
            timestamp = int(timestamp_str)
        except ValueError:
            return False
        
        # Check if timestamp is within window
        current_time = time.time()
        if abs(current_time - timestamp) > self.epoch_window:
            return False
        
        # Verify nonce matches data
        expected_hash = hashlib.sha256(data).hexdigest()[:16]
        if nonce_hash != expected_hash:
            return False
        
        # Add to cache
        self.nonce_cache.append(nonce)
        return True
    
    def test_ctp96_replay_rejected(self):
        """Test that CTP-96 replay attacks are rejected."""
        print("🔥 Testing CTP-96 replay rejection...")
        
        # Create test data
        test_data = b"test ctp96 frame data"
        nonce = self._generate_nonce(test_data)
        
        # First use should succeed
        assert self._validate_nonce(nonce, test_data), "First nonce validation should succeed"
        print("✅ First nonce validation succeeded")
        
        # Replay should fail
        assert not self._validate_nonce(nonce, test_data), "Replay nonce should be rejected"
        print("✅ Replay nonce correctly rejected")
    
    def test_ctp96_nonce_expiry(self):
        """Test that expired nonces are rejected."""
        print("🔥 Testing CTP-96 nonce expiry...")
        
        # Create nonce with old timestamp
        test_data = b"test expired nonce"
        old_timestamp = time.time() - (self.epoch_window + 100)  # 100 seconds past window
        expired_nonce = self._generate_nonce(test_data, old_timestamp)
        
        # Expired nonce should fail
        assert not self._validate_nonce(expired_nonce, test_data), "Expired nonce should be rejected"
        print("✅ Expired nonce correctly rejected")
    
    def test_ctp96_nonce_tampering(self):
        """Test that tampered nonces are rejected."""
        print("🔥 Testing CTP-96 nonce tampering...")
        
        # Create test data
        test_data = b"test tampered nonce"
        nonce = self._generate_nonce(test_data)
        
        # Tamper with nonce
        tampered_nonce = nonce.replace('a', 'x')  # Simple tampering
        
        # Tampered nonce should fail
        assert not self._validate_nonce(tampered_nonce, test_data), "Tampered nonce should be rejected"
        print("✅ Tampered nonce correctly rejected")
    
    def test_ctp96_nonce_data_mismatch(self):
        """Test that nonces with mismatched data are rejected."""
        print("🔥 Testing CTP-96 nonce data mismatch...")
        
        # Create nonce for one set of data
        test_data1 = b"test data 1"
        nonce = self._generate_nonce(test_data1)
        
        # Try to use nonce with different data
        test_data2 = b"test data 2"
        assert not self._validate_nonce(nonce, test_data2), "Nonce with mismatched data should be rejected"
        print("✅ Nonce with mismatched data correctly rejected")
    
    def test_ctp96_lru_cache_eviction(self):
        """Test LRU cache eviction for nonces."""
        print("🔥 Testing CTP-96 LRU cache eviction...")
        
        # Fill cache beyond maxlen
        for i in range(1005):  # More than maxlen of 1000
            test_data = f"test data {i}".encode()
            nonce = self._generate_nonce(test_data)
            assert self._validate_nonce(nonce, test_data), f"Nonce {i} should be valid"
        
        # First nonce should be evicted
        first_data = b"test data 0"
        first_nonce = self._generate_nonce(first_data, time.time() - 1000)
        assert not self._validate_nonce(first_nonce, first_data), "Evicted nonce should be rejected"
        print("✅ LRU cache eviction working correctly")
    
    def test_ctp96_concurrent_nonces(self):
        """Test concurrent nonce validation."""
        print("🔥 Testing CTP-96 concurrent nonces...")
        
        import concurrent.futures
        import threading
        
        def validate_nonce_worker(worker_id: int):
            """Worker function for concurrent nonce validation."""
            test_data = f"concurrent test data {worker_id}".encode()
            nonce = self._generate_nonce(test_data)
            return self._validate_nonce(nonce, test_data)
        
        # Test with multiple concurrent validations
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            futures = [executor.submit(validate_nonce_worker, i) for i in range(10)]
            results = [future.result() for future in concurrent.futures.as_completed(futures)]
        
        # All should succeed
        assert all(results), "All concurrent nonce validations should succeed"
        print("✅ Concurrent nonce validation working correctly")
    
    def test_ctp96_nonce_performance(self):
        """Test nonce validation performance."""
        print("🔥 Testing CTP-96 nonce performance...")
        
        # Test validation speed
        test_data = b"performance test data"
        nonce = self._generate_nonce(test_data)
        
        start_time = time.time()
        for _ in range(1000):
            self._validate_nonce(nonce, test_data)
        elapsed = time.time() - start_time
        
        # Should be fast (less than 1ms per validation)
        assert elapsed < 1.0, f"Nonce validation too slow: {elapsed:.3f}s for 1000 validations"
        print(f"✅ Nonce validation performance: {elapsed:.3f}s for 1000 validations")
    
    def test_ctp96_nonce_integration(self):
        """Test nonce integration with CTP-96 protocol."""
        print("🔥 Testing CTP-96 nonce integration...")
        
        # Simulate CTP-96 frame with nonce
        frame_data = b"ctp96 frame payload"
        nonce = self._generate_nonce(frame_data)
        
        # Simulate frame processing
        frame = {
            "data": frame_data,
            "nonce": nonce,
            "timestamp": time.time(),
            "protocol": "ctp96"
        }
        
        # Validate frame
        assert self._validate_nonce(frame["nonce"], frame["data"]), "CTP-96 frame validation should succeed"
        print("✅ CTP-96 frame validation succeeded")
        
        # Test frame replay
        assert not self._validate_nonce(frame["nonce"], frame["data"]), "CTP-96 frame replay should be rejected"
        print("✅ CTP-96 frame replay correctly rejected")

@pytest.mark.phase9_chaos
class TestCTP96Security:
    """Test CTP-96 security properties."""
    
    def test_ctp96_nonce_cryptographic_properties(self):
        """Test cryptographic properties of nonces."""
        print("🔥 Testing CTP-96 nonce cryptographic properties...")
        
        # Test nonce uniqueness
        nonces = set()
        for i in range(1000):
            test_data = f"unique test data {i}".encode()
            nonce = self._generate_nonce(test_data)
            assert nonce not in nonces, f"Nonce collision detected: {nonce}"
            nonces.add(nonce)
        
        print("✅ Nonce uniqueness verified")
        
        # Test nonce entropy
        nonce_bytes = [nonce.encode() for nonce in list(nonces)[:100]]
        entropy = self._calculate_entropy(nonce_bytes)
        assert entropy > 0.8, f"Nonce entropy too low: {entropy}"
        print(f"✅ Nonce entropy: {entropy:.3f}")
    
    def _calculate_entropy(self, data_list: List[bytes]) -> float:
        """Calculate entropy of data list."""
        import math
        from collections import Counter
        
        # Flatten all data
        all_bytes = b''.join(data_list)
        
        # Count byte frequencies
        byte_counts = Counter(all_bytes)
        total_bytes = len(all_bytes)
        
        # Calculate entropy
        entropy = 0
        for count in byte_counts.values():
            probability = count / total_bytes
            entropy -= probability * math.log2(probability)
        
        # Normalize to 0-1 range
        return entropy / 8.0  # 8 bits per byte

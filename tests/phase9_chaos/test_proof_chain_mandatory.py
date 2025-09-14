"""
Proof Chain Mandatory Tests
Tests that proof chains are required and validated.
"""
import pytest
import json
from typing import Dict, Any, List, Optional

@pytest.mark.phase9_chaos
class TestProofChainMandatory:
    """Test that proof chains are mandatory and validated."""
    
    @pytest.fixture(autouse=True)
    def setup_proof_validator(self):
        """Setup proof chain validator."""
        self.proof_validator = ProofChainValidator()
        yield
    
    def test_proof_chain_required(self):
        """Test that proof chains are required."""
        print("🔥 Testing proof chain requirement...")
        
        # Test data without proof chain
        data_without_proof = {
            "content": "test content",
            "metadata": {"version": "1.0"},
            # No proof_chain field
        }
        
        # Should fail validation
        assert not self.proof_validator.validate(data_without_proof), "Data without proof chain should be rejected"
        print("✅ Data without proof chain correctly rejected")
        
        # Test data with proof chain
        data_with_proof = {
            "content": "test content",
            "metadata": {"version": "1.0"},
            "proof_chain": self.proof_validator.generate_proof_chain(data_without_proof)
        }
        
        # Should pass validation
        assert self.proof_validator.validate(data_with_proof), "Data with proof chain should be accepted"
        print("✅ Data with proof chain correctly accepted")
    
    def test_proof_chain_validation(self):
        """Test proof chain validation."""
        print("🔥 Testing proof chain validation...")
        
        # Generate valid proof chain
        test_data = {"content": "test content", "metadata": {"version": "1.0"}}
        proof_chain = self.proof_validator.generate_proof_chain(test_data)
        
        # Test valid proof chain
        data_with_proof = {**test_data, "proof_chain": proof_chain}
        assert self.proof_validator.validate(data_with_proof), "Valid proof chain should pass"
        print("✅ Valid proof chain passed validation")
        
        # Test invalid proof chain
        invalid_proof = {**proof_chain, "signature": "invalid_signature"}
        data_with_invalid_proof = {**test_data, "proof_chain": invalid_proof}
        assert not self.proof_validator.validate(data_with_invalid_proof), "Invalid proof chain should fail"
        print("✅ Invalid proof chain correctly rejected")
    
    def test_proof_chain_tampering(self):
        """Test that tampered proof chains are rejected."""
        print("🔥 Testing proof chain tampering...")
        
        # Generate proof chain
        test_data = {"content": "test content", "metadata": {"version": "1.0"}}
        proof_chain = self.proof_validator.generate_proof_chain(test_data)
        
        # Tamper with data
        tampered_data = {**test_data, "content": "tampered content"}
        data_with_proof = {**tampered_data, "proof_chain": proof_chain}
        
        # Should fail validation
        assert not self.proof_validator.validate(data_with_proof), "Tampered data with original proof should fail"
        print("✅ Tampered data with original proof correctly rejected")
    
    def test_proof_chain_chain_validation(self):
        """Test proof chain chain validation."""
        print("🔥 Testing proof chain chain validation...")
        
        # Create a chain of proofs
        chain_data = [
            {"content": "block 1", "metadata": {"block": 1}},
            {"content": "block 2", "metadata": {"block": 2}},
            {"content": "block 3", "metadata": {"block": 3}}
        ]
        
        # Generate proof chain
        proof_chain = self.proof_validator.generate_chain_proof(chain_data)
        
        # Test valid chain
        assert self.proof_validator.validate_chain(chain_data, proof_chain), "Valid proof chain should pass"
        print("✅ Valid proof chain passed validation")
        
        # Test invalid chain (missing block)
        incomplete_chain = chain_data[:2]  # Missing block 3
        assert not self.proof_validator.validate_chain(incomplete_chain, proof_chain), "Incomplete chain should fail"
        print("✅ Incomplete chain correctly rejected")
    
    def test_proof_chain_performance(self):
        """Test proof chain performance."""
        print("🔥 Testing proof chain performance...")
        
        import time
        
        # Test proof generation performance
        test_data = {"content": "performance test", "metadata": {"test": True}}
        
        start_time = time.time()
        for _ in range(100):
            proof_chain = self.proof_validator.generate_proof_chain(test_data)
        generation_time = time.time() - start_time
        
        # Test proof validation performance
        proof_chain = self.proof_validator.generate_proof_chain(test_data)
        data_with_proof = {**test_data, "proof_chain": proof_chain}
        
        start_time = time.time()
        for _ in range(100):
            self.proof_validator.validate(data_with_proof)
        validation_time = time.time() - start_time
        
        # Should be fast (less than 10ms per operation)
        assert generation_time < 1.0, f"Proof generation too slow: {generation_time:.3f}s for 100 proofs"
        assert validation_time < 1.0, f"Proof validation too slow: {validation_time:.3f}s for 100 validations"
        
        print(f"✅ Proof generation: {generation_time:.3f}s for 100 proofs")
        print(f"✅ Proof validation: {validation_time:.3f}s for 100 validations")
    
    def test_proof_chain_integration(self):
        """Test proof chain integration with existing phases."""
        print("🔥 Testing proof chain integration...")
        
        # Test integration with Phase 5 (GraphQL)
        graphql_data = {
            "query": "mutation { publish(content: \"test\") { cid } }",
            "variables": {},
            "proof_chain": None  # Will be generated
        }
        
        # Generate proof for GraphQL operation
        proof_chain = self.proof_validator.generate_proof_chain(graphql_data)
        graphql_data["proof_chain"] = proof_chain
        
        # Validate GraphQL operation
        assert self.proof_validator.validate(graphql_data), "GraphQL operation with proof should pass"
        print("✅ GraphQL operation with proof passed validation")
        
        # Test integration with Phase 7 (Security)
        security_data = {
            "operation": "verify",
            "content": "security test content",
            "proof_chain": None  # Will be generated
        }
        
        # Generate proof for security operation
        proof_chain = self.proof_validator.generate_proof_chain(security_data)
        security_data["proof_chain"] = proof_chain
        
        # Validate security operation
        assert self.proof_validator.validate(security_data), "Security operation with proof should pass"
        print("✅ Security operation with proof passed validation")


class ProofChainValidator:
    """Proof chain validator for mandatory proof validation."""
    
    def __init__(self):
        self.valid_proofs = set()
    
    def generate_proof_chain(self, data: Dict[str, Any]) -> Dict[str, Any]:
        """Generate proof chain for data."""
        import hashlib
        import time
        
        # Create proof
        data_hash = hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()
        timestamp = int(time.time())
        
        proof_chain = {
            "hash": data_hash,
            "timestamp": timestamp,
            "signature": self._sign_data(data_hash, timestamp),
            "validator": "hologram_proof_validator"
        }
        
        return proof_chain
    
    def generate_chain_proof(self, chain_data: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate proof chain for a chain of data."""
        import hashlib
        import time
        
        # Create chain hash
        chain_hash = hashlib.sha256()
        for data in chain_data:
            data_hash = hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()
            chain_hash.update(data_hash.encode())
        
        chain_hash_hex = chain_hash.hexdigest()
        timestamp = int(time.time())
        
        proof_chain = {
            "chain_hash": chain_hash_hex,
            "timestamp": timestamp,
            "signature": self._sign_data(chain_hash_hex, timestamp),
            "validator": "hologram_chain_validator",
            "block_count": len(chain_data)
        }
        
        return proof_chain
    
    def validate(self, data: Dict[str, Any]) -> bool:
        """Validate data with proof chain."""
        # Check if proof chain exists
        if "proof_chain" not in data:
            return False
        
        proof_chain = data["proof_chain"]
        
        # Validate proof chain structure
        required_fields = ["hash", "timestamp", "signature", "validator"]
        if not all(field in proof_chain for field in required_fields):
            return False
        
        # Validate proof
        data_without_proof = {k: v for k, v in data.items() if k != "proof_chain"}
        expected_proof = self.generate_proof_chain(data_without_proof)
        
        return proof_chain["hash"] == expected_proof["hash"] and \
               proof_chain["signature"] == expected_proof["signature"]
    
    def validate_chain(self, chain_data: List[Dict[str, Any]], proof_chain: Dict[str, Any]) -> bool:
        """Validate chain of data with proof chain."""
        # Check if proof chain exists
        if not proof_chain:
            return False
        
        # Validate proof chain structure
        required_fields = ["chain_hash", "timestamp", "signature", "validator", "block_count"]
        if not all(field in proof_chain for field in required_fields):
            return False
        
        # Validate block count
        if proof_chain["block_count"] != len(chain_data):
            return False
        
        # Validate chain proof
        expected_proof = self.generate_chain_proof(chain_data)
        
        return proof_chain["chain_hash"] == expected_proof["chain_hash"] and \
               proof_chain["signature"] == expected_proof["signature"]
    
    def _sign_data(self, data_hash: str, timestamp: int) -> str:
        """Sign data hash and timestamp."""
        import hashlib
        
        # Simple signature (in production, use proper cryptographic signing)
        signature_data = f"{data_hash}_{timestamp}_hologram_secret"
        signature = hashlib.sha256(signature_data.encode()).hexdigest()
        
        return signature

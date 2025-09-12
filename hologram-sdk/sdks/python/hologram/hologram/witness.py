"""
Witness manager for cryptographic verification.
"""

from typing import Dict, Any, Optional, List
from .client import Client
from .errors import WitnessError


class WitnessManager:
    """
    Witness manager for creating and managing cryptographic witnesses.
    
    Witnesses provide cryptographic verification of object integrity and authenticity.
    """
    
    def __init__(self, client: Client):
        """
        Initialize witness manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def create(self, uor_id: str, witness_type: str = "integrity", metadata: Optional[Dict[str, Any]] = None) -> str:
        """
        Create a witness for a UOR-ID.
        
        Args:
            uor_id: UOR-ID to create witness for
            witness_type: Type of witness (integrity, authenticity, etc.)
            metadata: Optional metadata for the witness
            
        Returns:
            Witness ID string
            
        Raises:
            WitnessError: If witness creation fails
        """
        try:
            payload = {
                "uor_id": uor_id,
                "witness_type": witness_type,
                "metadata": metadata or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/witness/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["witness_id"]
            
        except Exception as e:
            raise WitnessError(f"Failed to create witness: {e}")
    
    def verify(self, witness_id: str, uor_id: str) -> Dict[str, Any]:
        """
        Verify a witness against a UOR-ID.
        
        Args:
            witness_id: Witness ID to verify
            uor_id: UOR-ID to verify against
            
        Returns:
            Verification result dictionary
            
        Raises:
            WitnessError: If witness verification fails
        """
        try:
            payload = {
                "witness_id": witness_id,
                "uor_id": uor_id
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/witness/verify",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise WitnessError(f"Failed to verify witness: {e}")
    
    def list(self, uor_id: Optional[str] = None, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List witnesses.
        
        Args:
            uor_id: Optional UOR-ID to filter witnesses by
            limit: Maximum number of witnesses to return
            offset: Number of witnesses to skip
            
        Returns:
            List of witness information dictionaries
            
        Raises:
            WitnessError: If listing witnesses fails
        """
        try:
            params = {}
            if uor_id is not None:
                params["uor_id"] = uor_id
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/witness/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise WitnessError(f"Failed to list witnesses: {e}")
    
    def delete(self, witness_id: str) -> bool:
        """
        Delete a witness.
        
        Args:
            witness_id: Witness ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            WitnessError: If witness deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/witness/delete/{witness_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise WitnessError(f"Failed to delete witness {witness_id}: {e}")
    
    def get_info(self, witness_id: str) -> Dict[str, Any]:
        """
        Get witness information.
        
        Args:
            witness_id: Witness ID to get information for
            
        Returns:
            Witness information dictionary
            
        Raises:
            WitnessError: If getting witness info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/witness/info/{witness_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise WitnessError(f"Failed to get witness info for {witness_id}: {e}")
    
    def update_metadata(self, witness_id: str, metadata: Dict[str, Any]) -> bool:
        """
        Update metadata for a witness.
        
        Args:
            witness_id: Witness ID to update
            metadata: New metadata
            
        Returns:
            True if update was successful
            
        Raises:
            WitnessError: If metadata update fails
        """
        try:
            payload = {"metadata": metadata}
            
            response = self.client.session.put(
                f"{self.client.base_url}/witness/update/{witness_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise WitnessError(f"Failed to update metadata for witness {witness_id}: {e}")
    
    def create_chain(self, uor_ids: List[str], chain_type: str = "integrity") -> str:
        """
        Create a witness chain for multiple UOR-IDs.
        
        Args:
            uor_ids: List of UOR-IDs to create witness chain for
            chain_type: Type of witness chain
            
        Returns:
            Witness chain ID string
            
        Raises:
            WitnessError: If witness chain creation fails
        """
        try:
            payload = {
                "uor_ids": uor_ids,
                "chain_type": chain_type
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/witness/chain/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["chain_id"]
            
        except Exception as e:
            raise WitnessError(f"Failed to create witness chain: {e}")
    
    def verify_chain(self, chain_id: str) -> Dict[str, Any]:
        """
        Verify a witness chain.
        
        Args:
            chain_id: Witness chain ID to verify
            
        Returns:
            Chain verification result dictionary
            
        Raises:
            WitnessError: If witness chain verification fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/witness/chain/verify/{chain_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise WitnessError(f"Failed to verify witness chain: {e}")
    
    def get_chain_info(self, chain_id: str) -> Dict[str, Any]:
        """
        Get witness chain information.
        
        Args:
            chain_id: Witness chain ID to get information for
            
        Returns:
            Witness chain information dictionary
            
        Raises:
            WitnessError: If getting witness chain info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/witness/chain/info/{chain_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise WitnessError(f"Failed to get witness chain info for {chain_id}: {e}")

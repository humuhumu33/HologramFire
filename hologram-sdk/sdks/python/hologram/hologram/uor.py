"""
UOR-ID (Universal Object Reference) manager.
"""

from typing import Dict, Any, Optional, List
from .client import Client
from .errors import UORIDError


class UORManager:
    """
    UOR-ID manager for creating and managing Universal Object References.
    
    UOR-IDs provide a universal way to reference objects across the Hologram ecosystem.
    """
    
    def __init__(self, client: Client):
        """
        Initialize UOR manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def create(self, object_ref: str, metadata: Optional[Dict[str, Any]] = None) -> str:
        """
        Create a UOR-ID for an object.
        
        Args:
            object_ref: Object reference (e.g., image name, container ID)
            metadata: Optional metadata for the UOR-ID
            
        Returns:
            UOR-ID string
            
        Raises:
            UORIDError: If UOR-ID creation fails
        """
        try:
            payload = {
                "object_ref": object_ref,
                "metadata": metadata or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/uor/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["uor_id"]
            
        except Exception as e:
            raise UORIDError(f"Failed to create UOR-ID: {e}")
    
    def resolve(self, uor_id: str) -> Dict[str, Any]:
        """
        Resolve a UOR-ID to its object information.
        
        Args:
            uor_id: UOR-ID to resolve
            
        Returns:
            Object information dictionary
            
        Raises:
            UORIDError: If UOR-ID resolution fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/uor/resolve/{uor_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise UORIDError(f"Failed to resolve UOR-ID {uor_id}: {e}")
    
    def list(self, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List UOR-IDs.
        
        Args:
            limit: Maximum number of UOR-IDs to return
            offset: Number of UOR-IDs to skip
            
        Returns:
            List of UOR-ID information dictionaries
            
        Raises:
            UORIDError: If listing UOR-IDs fails
        """
        try:
            params = {}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/uor/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise UORIDError(f"Failed to list UOR-IDs: {e}")
    
    def delete(self, uor_id: str) -> bool:
        """
        Delete a UOR-ID.
        
        Args:
            uor_id: UOR-ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            UORIDError: If UOR-ID deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/uor/delete/{uor_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise UORIDError(f"Failed to delete UOR-ID {uor_id}: {e}")
    
    def update_metadata(self, uor_id: str, metadata: Dict[str, Any]) -> bool:
        """
        Update metadata for a UOR-ID.
        
        Args:
            uor_id: UOR-ID to update
            metadata: New metadata
            
        Returns:
            True if update was successful
            
        Raises:
            UORIDError: If metadata update fails
        """
        try:
            payload = {"metadata": metadata}
            
            response = self.client.session.put(
                f"{self.client.base_url}/uor/update/{uor_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise UORIDError(f"Failed to update metadata for UOR-ID {uor_id}: {e}")
    
    def search(self, query: str, limit: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        Search UOR-IDs by query.
        
        Args:
            query: Search query
            limit: Maximum number of results to return
            
        Returns:
            List of matching UOR-ID information dictionaries
            
        Raises:
            UORIDError: If search fails
        """
        try:
            params = {"query": query}
            if limit is not None:
                params["limit"] = limit
            
            response = self.client.session.get(
                f"{self.client.base_url}/uor/search",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise UORIDError(f"Failed to search UOR-IDs: {e}")
    
    def get_relationships(self, uor_id: str) -> List[Dict[str, Any]]:
        """
        Get relationships for a UOR-ID.
        
        Args:
            uor_id: UOR-ID to get relationships for
            
        Returns:
            List of relationship information dictionaries
            
        Raises:
            UORIDError: If getting relationships fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/uor/relationships/{uor_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise UORIDError(f"Failed to get relationships for UOR-ID {uor_id}: {e}")
    
    def create_relationship(self, source_uor_id: str, target_uor_id: str, relationship_type: str) -> bool:
        """
        Create a relationship between two UOR-IDs.
        
        Args:
            source_uor_id: Source UOR-ID
            target_uor_id: Target UOR-ID
            relationship_type: Type of relationship
            
        Returns:
            True if relationship creation was successful
            
        Raises:
            UORIDError: If relationship creation fails
        """
        try:
            payload = {
                "source_uor_id": source_uor_id,
                "target_uor_id": target_uor_id,
                "relationship_type": relationship_type
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/uor/relationship",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise UORIDError(f"Failed to create relationship: {e}")

"""
VPI (Virtual Process Isolation) manager.
"""

from typing import Dict, Any, Optional, List
from .client import Client
from .errors import VPILeaseError


class VPIManager:
    """
    VPI manager for creating and managing Virtual Process Isolation leases.
    
    VPI leases provide secure process isolation and resource management.
    """
    
    def __init__(self, client: Client):
        """
        Initialize VPI manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def create_lease(self, uor_id: str, witness_id: str, lease_config: Optional[Dict[str, Any]] = None) -> str:
        """
        Create a VPI lease for a UOR-ID and witness.
        
        Args:
            uor_id: UOR-ID to create lease for
            witness_id: Witness ID to associate with lease
            lease_config: Optional lease configuration
            
        Returns:
            VPI lease ID string
            
        Raises:
            VPILeaseError: If VPI lease creation fails
        """
        try:
            payload = {
                "uor_id": uor_id,
                "witness_id": witness_id,
                "lease_config": lease_config or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/vpi/lease/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["lease_id"]
            
        except Exception as e:
            raise VPILeaseError(f"Failed to create VPI lease: {e}")
    
    def activate(self, lease_id: str) -> bool:
        """
        Activate a VPI lease.
        
        Args:
            lease_id: VPI lease ID to activate
            
        Returns:
            True if activation was successful
            
        Raises:
            VPILeaseError: If VPI lease activation fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/vpi/lease/activate/{lease_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VPILeaseError(f"Failed to activate VPI lease {lease_id}: {e}")
    
    def deactivate(self, lease_id: str) -> bool:
        """
        Deactivate a VPI lease.
        
        Args:
            lease_id: VPI lease ID to deactivate
            
        Returns:
            True if deactivation was successful
            
        Raises:
            VPILeaseError: If VPI lease deactivation fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/vpi/lease/deactivate/{lease_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VPILeaseError(f"Failed to deactivate VPI lease {lease_id}: {e}")
    
    def list(self, uor_id: Optional[str] = None, status: Optional[str] = None, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List VPI leases.
        
        Args:
            uor_id: Optional UOR-ID to filter leases by
            status: Optional status to filter leases by
            limit: Maximum number of leases to return
            offset: Number of leases to skip
            
        Returns:
            List of VPI lease information dictionaries
            
        Raises:
            VPILeaseError: If listing VPI leases fails
        """
        try:
            params = {}
            if uor_id is not None:
                params["uor_id"] = uor_id
            if status is not None:
                params["status"] = status
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/vpi/lease/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VPILeaseError(f"Failed to list VPI leases: {e}")
    
    def get_info(self, lease_id: str) -> Dict[str, Any]:
        """
        Get VPI lease information.
        
        Args:
            lease_id: VPI lease ID to get information for
            
        Returns:
            VPI lease information dictionary
            
        Raises:
            VPILeaseError: If getting VPI lease info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/vpi/lease/info/{lease_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VPILeaseError(f"Failed to get VPI lease info for {lease_id}: {e}")
    
    def delete(self, lease_id: str) -> bool:
        """
        Delete a VPI lease.
        
        Args:
            lease_id: VPI lease ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            VPILeaseError: If VPI lease deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/vpi/lease/delete/{lease_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VPILeaseError(f"Failed to delete VPI lease {lease_id}: {e}")
    
    def update_config(self, lease_id: str, lease_config: Dict[str, Any]) -> bool:
        """
        Update configuration for a VPI lease.
        
        Args:
            lease_id: VPI lease ID to update
            lease_config: New lease configuration
            
        Returns:
            True if update was successful
            
        Raises:
            VPILeaseError: If VPI lease config update fails
        """
        try:
            payload = {"lease_config": lease_config}
            
            response = self.client.session.put(
                f"{self.client.base_url}/vpi/lease/update/{lease_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VPILeaseError(f"Failed to update config for VPI lease {lease_id}: {e}")
    
    def get_metrics(self, lease_id: str) -> Dict[str, Any]:
        """
        Get metrics for a VPI lease.
        
        Args:
            lease_id: VPI lease ID to get metrics for
            
        Returns:
            VPI lease metrics dictionary
            
        Raises:
            VPILeaseError: If getting VPI lease metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/vpi/lease/metrics/{lease_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VPILeaseError(f"Failed to get metrics for VPI lease {lease_id}: {e}")
    
    def create_pool(self, pool_config: Dict[str, Any]) -> str:
        """
        Create a VPI lease pool.
        
        Args:
            pool_config: Pool configuration
            
        Returns:
            VPI lease pool ID string
            
        Raises:
            VPILeaseError: If VPI lease pool creation fails
        """
        try:
            payload = {"pool_config": pool_config}
            
            response = self.client.session.post(
                f"{self.client.base_url}/vpi/pool/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["pool_id"]
            
        except Exception as e:
            raise VPILeaseError(f"Failed to create VPI lease pool: {e}")
    
    def get_pool_info(self, pool_id: str) -> Dict[str, Any]:
        """
        Get VPI lease pool information.
        
        Args:
            pool_id: VPI lease pool ID to get information for
            
        Returns:
            VPI lease pool information dictionary
            
        Raises:
            VPILeaseError: If getting VPI lease pool info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/vpi/pool/info/{pool_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VPILeaseError(f"Failed to get VPI lease pool info for {pool_id}: {e}")
    
    def list_pools(self, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List VPI lease pools.
        
        Args:
            limit: Maximum number of pools to return
            offset: Number of pools to skip
            
        Returns:
            List of VPI lease pool information dictionaries
            
        Raises:
            VPILeaseError: If listing VPI lease pools fails
        """
        try:
            params = {}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/vpi/pool/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VPILeaseError(f"Failed to list VPI lease pools: {e}")

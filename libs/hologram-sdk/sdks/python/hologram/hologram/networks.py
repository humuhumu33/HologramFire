"""
Network manager for native Hologram SDK.
"""

from typing import Dict, Any, Optional, List
from .client import Client
from .errors import NetworkError


class NetworkManager:
    """
    Network manager with native Hologram support.
    
    This manager provides network operations with first-class support for
    CTP-96 transport and Hologram-specific features.
    """
    
    def __init__(self, client: Client):
        """
        Initialize network manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def create(
        self,
        name: str,
        driver: str = "bridge",
        ctp96: bool = False,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Create a network with Hologram features.
        
        Args:
            name: Network name
            driver: Network driver
            ctp96: Whether to enable CTP-96 transport
            **kwargs: Additional network options
            
        Returns:
            Network creation response
            
        Raises:
            NetworkError: If network creation fails
        """
        try:
            payload = {
                "name": name,
                "driver": driver,
                "ctp96": ctp96,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/networks/create",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise NetworkError(f"Failed to create network: {e}")
    
    def list(self, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List networks.
        
        Args:
            limit: Maximum number of networks to return
            offset: Number of networks to skip
            
        Returns:
            List of network information dictionaries
            
        Raises:
            NetworkError: If listing networks fails
        """
        try:
            params = {}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/networks/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise NetworkError(f"Failed to list networks: {e}")
    
    def get_info(self, network_id: str) -> Dict[str, Any]:
        """
        Get network information.
        
        Args:
            network_id: Network ID to get information for
            
        Returns:
            Network information dictionary
            
        Raises:
            NetworkError: If getting network info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/networks/info/{network_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise NetworkError(f"Failed to get network info for {network_id}: {e}")
    
    def remove(self, network_id: str, force: bool = False) -> bool:
        """
        Remove a network.
        
        Args:
            network_id: Network ID to remove
            force: Whether to force removal
            
        Returns:
            True if removal was successful
            
        Raises:
            NetworkError: If network removal fails
        """
        try:
            params = {"force": force}
            
            response = self.client.session.delete(
                f"{self.client.base_url}/networks/remove/{network_id}",
                params=params
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise NetworkError(f"Failed to remove network {network_id}: {e}")
    
    def connect(self, network_id: str, container_id: str, **kwargs) -> bool:
        """
        Connect a container to a network.
        
        Args:
            network_id: Network ID to connect to
            container_id: Container ID to connect
            **kwargs: Additional connection options
            
        Returns:
            True if connection was successful
            
        Raises:
            NetworkError: If network connection fails
        """
        try:
            payload = {
                "container_id": container_id,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/networks/connect/{network_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise NetworkError(f"Failed to connect container to network: {e}")
    
    def disconnect(self, network_id: str, container_id: str, force: bool = False) -> bool:
        """
        Disconnect a container from a network.
        
        Args:
            network_id: Network ID to disconnect from
            container_id: Container ID to disconnect
            force: Whether to force disconnection
            
        Returns:
            True if disconnection was successful
            
        Raises:
            NetworkError: If network disconnection fails
        """
        try:
            params = {"force": force}
            
            response = self.client.session.post(
                f"{self.client.base_url}/networks/disconnect/{network_id}/{container_id}",
                params=params
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise NetworkError(f"Failed to disconnect container from network: {e}")
    
    def get_hologram_info(self, network_id: str) -> Dict[str, Any]:
        """
        Get Hologram-specific information for a network.
        
        Args:
            network_id: Network ID to get Hologram info for
            
        Returns:
            Hologram information dictionary
            
        Raises:
            NetworkError: If getting Hologram info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/networks/hologram/{network_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise NetworkError(f"Failed to get Hologram info for network {network_id}: {e}")
    
    def update_hologram_config(self, network_id: str, config: Dict[str, Any]) -> bool:
        """
        Update Hologram configuration for a network.
        
        Args:
            network_id: Network ID to update
            config: New Hologram configuration
            
        Returns:
            True if update was successful
            
        Raises:
            NetworkError: If Hologram config update fails
        """
        try:
            payload = {"config": config}
            
            response = self.client.session.put(
                f"{self.client.base_url}/networks/hologram/{network_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise NetworkError(f"Failed to update Hologram config for network {network_id}: {e}")
    
    def get_metrics(self, network_id: str) -> Dict[str, Any]:
        """
        Get network metrics.
        
        Args:
            network_id: Network ID to get metrics for
            
        Returns:
            Network metrics dictionary
            
        Raises:
            NetworkError: If getting network metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/networks/metrics/{network_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise NetworkError(f"Failed to get metrics for network {network_id}: {e}")
    
    def create_ctp96_tunnel(self, network_id: str, tunnel_config: Dict[str, Any]) -> str:
        """
        Create a CTP-96 tunnel on a network.
        
        Args:
            network_id: Network ID to create tunnel on
            tunnel_config: Tunnel configuration
            
        Returns:
            Tunnel ID string
            
        Raises:
            NetworkError: If CTP-96 tunnel creation fails
        """
        try:
            payload = {"tunnel_config": tunnel_config}
            
            response = self.client.session.post(
                f"{self.client.base_url}/networks/ctp96/tunnel/{network_id}",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["tunnel_id"]
            
        except Exception as e:
            raise NetworkError(f"Failed to create CTP-96 tunnel: {e}")
    
    def delete_ctp96_tunnel(self, network_id: str, tunnel_id: str) -> bool:
        """
        Delete a CTP-96 tunnel from a network.
        
        Args:
            network_id: Network ID to delete tunnel from
            tunnel_id: Tunnel ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            NetworkError: If CTP-96 tunnel deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/networks/ctp96/tunnel/{network_id}/{tunnel_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise NetworkError(f"Failed to delete CTP-96 tunnel: {e}")
    
    def list_ctp96_tunnels(self, network_id: str) -> List[Dict[str, Any]]:
        """
        List CTP-96 tunnels on a network.
        
        Args:
            network_id: Network ID to list tunnels for
            
        Returns:
            List of tunnel information dictionaries
            
        Raises:
            NetworkError: If listing CTP-96 tunnels fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/networks/ctp96/tunnels/{network_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise NetworkError(f"Failed to list CTP-96 tunnels: {e}")

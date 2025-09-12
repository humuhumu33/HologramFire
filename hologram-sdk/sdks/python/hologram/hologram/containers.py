"""
Container manager for native Hologram SDK.
"""

from typing import Dict, Any, Optional, List, Union
from .client import Client
from .errors import ContainerError


class ContainerManager:
    """
    Container manager with native Hologram support.
    
    This manager provides container operations with first-class support for
    UOR-IDs, witnesses, VPI leases, and CTP-96 transport.
    """
    
    def __init__(self, client: Client):
        """
        Initialize container manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def create(
        self,
        image: str,
        command: Optional[Union[str, List[str]]] = None,
        uor_id: Optional[str] = None,
        witness: Optional[str] = None,
        vpi_lease: Optional[str] = None,
        transport: str = "default",
        **kwargs
    ) -> Dict[str, Any]:
        """
        Create a container with Hologram features.
        
        Args:
            image: Image name or UOR-ID
            command: Command to run
            uor_id: Optional UOR-ID for the container
            witness: Optional witness for verification
            vpi_lease: Optional VPI lease for isolation
            transport: Transport type (default, ctp96)
            **kwargs: Additional container options
            
        Returns:
            Container creation response
            
        Raises:
            ContainerError: If container creation fails
        """
        try:
            payload = {
                "image": image,
                "command": command,
                "uor_id": uor_id,
                "witness": witness,
                "vpi_lease": vpi_lease,
                "transport": transport,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/containers/create",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ContainerError(f"Failed to create container: {e}")
    
    def start(self, container_id: str, transport: str = "default") -> bool:
        """
        Start a container with specified transport.
        
        Args:
            container_id: Container ID to start
            transport: Transport type (default, ctp96)
            
        Returns:
            True if start was successful
            
        Raises:
            ContainerError: If container start fails
        """
        try:
            payload = {"transport": transport}
            
            response = self.client.session.post(
                f"{self.client.base_url}/containers/start/{container_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ContainerError(f"Failed to start container {container_id}: {e}")
    
    def stop(self, container_id: str, timeout: Optional[int] = None) -> bool:
        """
        Stop a container.
        
        Args:
            container_id: Container ID to stop
            timeout: Optional timeout for stop operation
            
        Returns:
            True if stop was successful
            
        Raises:
            ContainerError: If container stop fails
        """
        try:
            params = {}
            if timeout is not None:
                params["timeout"] = timeout
            
            response = self.client.session.post(
                f"{self.client.base_url}/containers/stop/{container_id}",
                params=params
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ContainerError(f"Failed to stop container {container_id}: {e}")
    
    def remove(self, container_id: str, force: bool = False) -> bool:
        """
        Remove a container.
        
        Args:
            container_id: Container ID to remove
            force: Whether to force removal
            
        Returns:
            True if removal was successful
            
        Raises:
            ContainerError: If container removal fails
        """
        try:
            params = {"force": force}
            
            response = self.client.session.delete(
                f"{self.client.base_url}/containers/remove/{container_id}",
                params=params
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ContainerError(f"Failed to remove container {container_id}: {e}")
    
    def list(self, all: bool = False, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List containers.
        
        Args:
            all: Whether to include stopped containers
            limit: Maximum number of containers to return
            offset: Number of containers to skip
            
        Returns:
            List of container information dictionaries
            
        Raises:
            ContainerError: If listing containers fails
        """
        try:
            params = {"all": all}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/containers/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ContainerError(f"Failed to list containers: {e}")
    
    def get_info(self, container_id: str) -> Dict[str, Any]:
        """
        Get container information.
        
        Args:
            container_id: Container ID to get information for
            
        Returns:
            Container information dictionary
            
        Raises:
            ContainerError: If getting container info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/containers/info/{container_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ContainerError(f"Failed to get container info for {container_id}: {e}")
    
    def get_logs(self, container_id: str, follow: bool = False, tail: Optional[int] = None) -> str:
        """
        Get container logs.
        
        Args:
            container_id: Container ID to get logs for
            follow: Whether to follow logs
            tail: Number of lines to return from end
            
        Returns:
            Container logs
            
        Raises:
            ContainerError: If getting container logs fails
        """
        try:
            params = {"follow": follow}
            if tail is not None:
                params["tail"] = tail
            
            response = self.client.session.get(
                f"{self.client.base_url}/containers/logs/{container_id}",
                params=params
            )
            response.raise_for_status()
            
            return response.text
            
        except Exception as e:
            raise ContainerError(f"Failed to get logs for container {container_id}: {e}")
    
    def exec(self, container_id: str, command: Union[str, List[str]], **kwargs) -> Dict[str, Any]:
        """
        Execute a command in a container.
        
        Args:
            container_id: Container ID to execute command in
            command: Command to execute
            **kwargs: Additional exec options
            
        Returns:
            Execution result dictionary
            
        Raises:
            ContainerError: If command execution fails
        """
        try:
            payload = {
                "command": command,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/containers/exec/{container_id}",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ContainerError(f"Failed to execute command in container {container_id}: {e}")
    
    def get_metrics(self, container_id: str) -> Dict[str, Any]:
        """
        Get container metrics.
        
        Args:
            container_id: Container ID to get metrics for
            
        Returns:
            Container metrics dictionary
            
        Raises:
            ContainerError: If getting container metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/containers/metrics/{container_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ContainerError(f"Failed to get metrics for container {container_id}: {e}")
    
    def get_hologram_info(self, container_id: str) -> Dict[str, Any]:
        """
        Get Hologram-specific information for a container.
        
        Args:
            container_id: Container ID to get Hologram info for
            
        Returns:
            Hologram information dictionary
            
        Raises:
            ContainerError: If getting Hologram info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/containers/hologram/{container_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ContainerError(f"Failed to get Hologram info for container {container_id}: {e}")
    
    def update_hologram_config(self, container_id: str, config: Dict[str, Any]) -> bool:
        """
        Update Hologram configuration for a container.
        
        Args:
            container_id: Container ID to update
            config: New Hologram configuration
            
        Returns:
            True if update was successful
            
        Raises:
            ContainerError: If Hologram config update fails
        """
        try:
            payload = {"config": config}
            
            response = self.client.session.put(
                f"{self.client.base_url}/containers/hologram/{container_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ContainerError(f"Failed to update Hologram config for container {container_id}: {e}")

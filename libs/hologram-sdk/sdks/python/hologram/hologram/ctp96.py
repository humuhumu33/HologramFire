"""
CTP-96 transport manager.
"""

from typing import Dict, Any, Optional, List, Callable
from .client import Client
from .errors import CTP96Error


class CTP96Manager:
    """
    CTP-96 transport manager for efficient Hologram object transport.
    
    CTP-96 provides optimized transport for Hologram objects with built-in
    compression, encryption, and error correction.
    """
    
    def __init__(self, client: Client):
        """
        Initialize CTP-96 manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
        self._connections = {}
    
    def connect(self, host: str, port: int = 2376, config: Optional[Dict[str, Any]] = None) -> str:
        """
        Create a CTP-96 connection to a remote host.
        
        Args:
            host: Remote host address
            port: Remote port (default: 2376)
            config: Optional connection configuration
            
        Returns:
            Connection ID string
            
        Raises:
            CTP96Error: If connection creation fails
        """
        try:
            payload = {
                "host": host,
                "port": port,
                "config": config or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/ctp96/connect",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            connection_id = result["connection_id"]
            
            # Store connection info
            self._connections[connection_id] = {
                "host": host,
                "port": port,
                "config": config or {},
                "status": "connected"
            }
            
            return connection_id
            
        except Exception as e:
            raise CTP96Error(f"Failed to create CTP-96 connection: {e}")
    
    def disconnect(self, connection_id: str) -> bool:
        """
        Disconnect a CTP-96 connection.
        
        Args:
            connection_id: Connection ID to disconnect
            
        Returns:
            True if disconnection was successful
            
        Raises:
            CTP96Error: If disconnection fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/ctp96/disconnect/{connection_id}"
            )
            response.raise_for_status()
            
            # Remove connection from local cache
            if connection_id in self._connections:
                del self._connections[connection_id]
            
            return True
            
        except Exception as e:
            raise CTP96Error(f"Failed to disconnect CTP-96 connection {connection_id}: {e}")
    
    def send(self, connection_id: str, data: Any, metadata: Optional[Dict[str, Any]] = None) -> bool:
        """
        Send data via CTP-96 connection.
        
        Args:
            connection_id: Connection ID to send data through
            data: Data to send
            metadata: Optional metadata for the data
            
        Returns:
            True if send was successful
            
        Raises:
            CTP96Error: If send fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "data": data,
                "metadata": metadata or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/ctp96/send",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise CTP96Error(f"Failed to send data via CTP-96: {e}")
    
    def receive(self, connection_id: str, timeout: Optional[int] = None) -> Dict[str, Any]:
        """
        Receive data via CTP-96 connection.
        
        Args:
            connection_id: Connection ID to receive data from
            timeout: Optional timeout for receive operation
            
        Returns:
            Received data dictionary
            
        Raises:
            CTP96Error: If receive fails
        """
        try:
            params = {"connection_id": connection_id}
            if timeout is not None:
                params["timeout"] = timeout
            
            response = self.client.session.get(
                f"{self.client.base_url}/ctp96/receive",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise CTP96Error(f"Failed to receive data via CTP-96: {e}")
    
    def subscribe(self, connection_id: str, event_type: str, callback: Callable[[Dict[str, Any]], None]) -> str:
        """
        Subscribe to events on a CTP-96 connection.
        
        Args:
            connection_id: Connection ID to subscribe to
            event_type: Type of events to subscribe to
            callback: Callback function for events
            
        Returns:
            Subscription ID string
            
        Raises:
            CTP96Error: If subscription fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "event_type": event_type
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/ctp96/subscribe",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            subscription_id = result["subscription_id"]
            
            # Store subscription info
            if connection_id not in self._connections:
                self._connections[connection_id] = {}
            
            if "subscriptions" not in self._connections[connection_id]:
                self._connections[connection_id]["subscriptions"] = {}
            
            self._connections[connection_id]["subscriptions"][subscription_id] = {
                "event_type": event_type,
                "callback": callback
            }
            
            return subscription_id
            
        except Exception as e:
            raise CTP96Error(f"Failed to subscribe to CTP-96 events: {e}")
    
    def unsubscribe(self, connection_id: str, subscription_id: str) -> bool:
        """
        Unsubscribe from events on a CTP-96 connection.
        
        Args:
            connection_id: Connection ID to unsubscribe from
            subscription_id: Subscription ID to remove
            
        Returns:
            True if unsubscription was successful
            
        Raises:
            CTP96Error: If unsubscription fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/ctp96/unsubscribe/{connection_id}/{subscription_id}"
            )
            response.raise_for_status()
            
            # Remove subscription from local cache
            if connection_id in self._connections and "subscriptions" in self._connections[connection_id]:
                if subscription_id in self._connections[connection_id]["subscriptions"]:
                    del self._connections[connection_id]["subscriptions"][subscription_id]
            
            return True
            
        except Exception as e:
            raise CTP96Error(f"Failed to unsubscribe from CTP-96 events: {e}")
    
    def list_connections(self) -> List[Dict[str, Any]]:
        """
        List active CTP-96 connections.
        
        Returns:
            List of connection information dictionaries
            
        Raises:
            CTP96Error: If listing connections fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/ctp96/connections"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise CTP96Error(f"Failed to list CTP-96 connections: {e}")
    
    def get_connection_info(self, connection_id: str) -> Dict[str, Any]:
        """
        Get information about a CTP-96 connection.
        
        Args:
            connection_id: Connection ID to get information for
            
        Returns:
            Connection information dictionary
            
        Raises:
            CTP96Error: If getting connection info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/ctp96/connection/{connection_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise CTP96Error(f"Failed to get CTP-96 connection info for {connection_id}: {e}")
    
    def get_metrics(self, connection_id: str) -> Dict[str, Any]:
        """
        Get metrics for a CTP-96 connection.
        
        Args:
            connection_id: Connection ID to get metrics for
            
        Returns:
            Connection metrics dictionary
            
        Raises:
            CTP96Error: If getting connection metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/ctp96/metrics/{connection_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise CTP96Error(f"Failed to get CTP-96 connection metrics for {connection_id}: {e}")
    
    def create_tunnel(self, source_connection_id: str, target_connection_id: str, tunnel_config: Optional[Dict[str, Any]] = None) -> str:
        """
        Create a tunnel between two CTP-96 connections.
        
        Args:
            source_connection_id: Source connection ID
            target_connection_id: Target connection ID
            tunnel_config: Optional tunnel configuration
            
        Returns:
            Tunnel ID string
            
        Raises:
            CTP96Error: If tunnel creation fails
        """
        try:
            payload = {
                "source_connection_id": source_connection_id,
                "target_connection_id": target_connection_id,
                "tunnel_config": tunnel_config or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/ctp96/tunnel/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["tunnel_id"]
            
        except Exception as e:
            raise CTP96Error(f"Failed to create CTP-96 tunnel: {e}")
    
    def delete_tunnel(self, tunnel_id: str) -> bool:
        """
        Delete a CTP-96 tunnel.
        
        Args:
            tunnel_id: Tunnel ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            CTP96Error: If tunnel deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/ctp96/tunnel/delete/{tunnel_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise CTP96Error(f"Failed to delete CTP-96 tunnel {tunnel_id}: {e}")
    
    def list_tunnels(self) -> List[Dict[str, Any]]:
        """
        List active CTP-96 tunnels.
        
        Returns:
            List of tunnel information dictionaries
            
        Raises:
            CTP96Error: If listing tunnels fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/ctp96/tunnels"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise CTP96Error(f"Failed to list CTP-96 tunnels: {e}")

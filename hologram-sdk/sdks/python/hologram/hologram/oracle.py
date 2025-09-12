"""
Oracle manager for enhanced functionality.
"""

from typing import Dict, Any, Optional, List, Callable
from .client import Client
from .errors import OracleError


class OracleManager:
    """
    Oracle manager for enhanced Hologram functionality.
    
    Oracles provide enhanced functionality including advanced queries,
    event subscriptions, and intelligent recommendations.
    """
    
    def __init__(self, client: Client):
        """
        Initialize oracle manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
        self._connections = {}
        self._callbacks = {}
    
    def connect(self, oracle_host: str, oracle_port: int = 2377, config: Optional[Dict[str, Any]] = None) -> str:
        """
        Connect to a Hologram oracle.
        
        Args:
            oracle_host: Oracle host address
            oracle_port: Oracle port (default: 2377)
            config: Optional connection configuration
            
        Returns:
            Connection ID string
            
        Raises:
            OracleError: If oracle connection fails
        """
        try:
            payload = {
                "oracle_host": oracle_host,
                "oracle_port": oracle_port,
                "config": config or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/connect",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            connection_id = result["connection_id"]
            
            # Store connection info
            self._connections[connection_id] = {
                "oracle_host": oracle_host,
                "oracle_port": oracle_port,
                "config": config or {},
                "status": "connected"
            }
            
            return connection_id
            
        except Exception as e:
            raise OracleError(f"Failed to connect to oracle: {e}")
    
    def disconnect(self, connection_id: str) -> bool:
        """
        Disconnect from a Hologram oracle.
        
        Args:
            connection_id: Connection ID to disconnect
            
        Returns:
            True if disconnection was successful
            
        Raises:
            OracleError: If oracle disconnection fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/disconnect/{connection_id}"
            )
            response.raise_for_status()
            
            # Remove connection from local cache
            if connection_id in self._connections:
                del self._connections[connection_id]
            
            return True
            
        except Exception as e:
            raise OracleError(f"Failed to disconnect from oracle: {e}")
    
    def query(self, connection_id: str, query: str, params: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """
        Query a Hologram oracle.
        
        Args:
            connection_id: Oracle connection ID
            query: Query string
            params: Optional query parameters
            
        Returns:
            Query result dictionary
            
        Raises:
            OracleError: If oracle query fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "query": query,
                "params": params or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/query",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to query oracle: {e}")
    
    def subscribe(self, connection_id: str, event_type: str, callback: Callable[[Dict[str, Any]], None]) -> str:
        """
        Subscribe to oracle events.
        
        Args:
            connection_id: Oracle connection ID
            event_type: Type of events to subscribe to
            callback: Callback function for events
            
        Returns:
            Subscription ID string
            
        Raises:
            OracleError: If oracle subscription fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "event_type": event_type
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/subscribe",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            subscription_id = result["subscription_id"]
            
            # Store subscription info
            if connection_id not in self._callbacks:
                self._callbacks[connection_id] = {}
            
            self._callbacks[connection_id][subscription_id] = {
                "event_type": event_type,
                "callback": callback
            }
            
            return subscription_id
            
        except Exception as e:
            raise OracleError(f"Failed to subscribe to oracle events: {e}")
    
    def unsubscribe(self, connection_id: str, subscription_id: str) -> bool:
        """
        Unsubscribe from oracle events.
        
        Args:
            connection_id: Oracle connection ID
            subscription_id: Subscription ID to remove
            
        Returns:
            True if unsubscription was successful
            
        Raises:
            OracleError: If oracle unsubscription fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/oracle/unsubscribe/{connection_id}/{subscription_id}"
            )
            response.raise_for_status()
            
            # Remove subscription from local cache
            if connection_id in self._callbacks and subscription_id in self._callbacks[connection_id]:
                del self._callbacks[connection_id][subscription_id]
            
            return True
            
        except Exception as e:
            raise OracleError(f"Failed to unsubscribe from oracle events: {e}")
    
    def get_recommendations(self, connection_id: str, context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        Get recommendations from a Hologram oracle.
        
        Args:
            connection_id: Oracle connection ID
            context: Context for recommendations
            
        Returns:
            List of recommendation dictionaries
            
        Raises:
            OracleError: If getting recommendations fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "context": context
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/recommendations",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to get oracle recommendations: {e}")
    
    def get_insights(self, connection_id: str, data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Get insights from a Hologram oracle.
        
        Args:
            connection_id: Oracle connection ID
            data: Data to analyze
            
        Returns:
            Insights dictionary
            
        Raises:
            OracleError: If getting insights fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "data": data
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/insights",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to get oracle insights: {e}")
    
    def list_connections(self) -> List[Dict[str, Any]]:
        """
        List active oracle connections.
        
        Returns:
            List of connection information dictionaries
            
        Raises:
            OracleError: If listing connections fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/oracle/connections"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to list oracle connections: {e}")
    
    def get_connection_info(self, connection_id: str) -> Dict[str, Any]:
        """
        Get information about an oracle connection.
        
        Args:
            connection_id: Connection ID to get information for
            
        Returns:
            Connection information dictionary
            
        Raises:
            OracleError: If getting connection info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/oracle/connection/{connection_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to get oracle connection info for {connection_id}: {e}")
    
    def get_metrics(self, connection_id: str) -> Dict[str, Any]:
        """
        Get metrics for an oracle connection.
        
        Args:
            connection_id: Connection ID to get metrics for
            
        Returns:
            Connection metrics dictionary
            
        Raises:
            OracleError: If getting connection metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/oracle/metrics/{connection_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to get oracle connection metrics for {connection_id}: {e}")
    
    def create_workflow(self, connection_id: str, workflow_config: Dict[str, Any]) -> str:
        """
        Create a workflow on a Hologram oracle.
        
        Args:
            connection_id: Oracle connection ID
            workflow_config: Workflow configuration
            
        Returns:
            Workflow ID string
            
        Raises:
            OracleError: If workflow creation fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "workflow_config": workflow_config
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/workflow/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["workflow_id"]
            
        except Exception as e:
            raise OracleError(f"Failed to create oracle workflow: {e}")
    
    def execute_workflow(self, connection_id: str, workflow_id: str, input_data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Execute a workflow on a Hologram oracle.
        
        Args:
            connection_id: Oracle connection ID
            workflow_id: Workflow ID to execute
            input_data: Input data for workflow
            
        Returns:
            Workflow execution result dictionary
            
        Raises:
            OracleError: If workflow execution fails
        """
        try:
            payload = {
                "connection_id": connection_id,
                "workflow_id": workflow_id,
                "input_data": input_data
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/oracle/workflow/execute",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to execute oracle workflow: {e}")
    
    def get_workflow_status(self, connection_id: str, workflow_id: str) -> Dict[str, Any]:
        """
        Get workflow execution status.
        
        Args:
            connection_id: Oracle connection ID
            workflow_id: Workflow ID to get status for
            
        Returns:
            Workflow status dictionary
            
        Raises:
            OracleError: If getting workflow status fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/oracle/workflow/status/{connection_id}/{workflow_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise OracleError(f"Failed to get workflow status: {e}")

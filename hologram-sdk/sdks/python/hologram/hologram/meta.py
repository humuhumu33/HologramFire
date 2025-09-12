"""
Meta-awareness manager.
"""

from typing import Dict, Any, Optional, List, Callable
from .client import Client
from .errors import MetaError


class MetaManager:
    """
    Meta-awareness manager for self-monitoring and optimization.
    
    Meta-awareness provides self-monitoring, optimization, and self-healing
    capabilities for the Hologram system.
    """
    
    def __init__(self, client: Client):
        """
        Initialize meta-awareness manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
        self._enabled = False
        self._callbacks = {}
    
    def enable(self, config: Optional[Dict[str, Any]] = None) -> bool:
        """
        Enable meta-awareness.
        
        Args:
            config: Optional meta-awareness configuration
            
        Returns:
            True if meta-awareness was enabled successfully
            
        Raises:
            MetaError: If meta-awareness enable fails
        """
        try:
            payload = {
                "enabled": True,
                "config": config or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/meta/enable",
                json=payload
            )
            response.raise_for_status()
            
            self._enabled = True
            return True
            
        except Exception as e:
            raise MetaError(f"Failed to enable meta-awareness: {e}")
    
    def disable(self) -> bool:
        """
        Disable meta-awareness.
        
        Returns:
            True if meta-awareness was disabled successfully
            
        Raises:
            MetaError: If meta-awareness disable fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/meta/disable"
            )
            response.raise_for_status()
            
            self._enabled = False
            return True
            
        except Exception as e:
            raise MetaError(f"Failed to disable meta-awareness: {e}")
    
    def configure(self, config: Dict[str, Any]) -> bool:
        """
        Configure meta-awareness.
        
        Args:
            config: Meta-awareness configuration
            
        Returns:
            True if configuration was successful
            
        Raises:
            MetaError: If meta-awareness configuration fails
        """
        try:
            payload = {"config": config}
            
            response = self.client.session.put(
                f"{self.client.base_url}/meta/configure",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise MetaError(f"Failed to configure meta-awareness: {e}")
    
    def get_data(self) -> Dict[str, Any]:
        """
        Get meta-awareness data.
        
        Returns:
            Meta-awareness data dictionary
            
        Raises:
            MetaError: If getting meta-awareness data fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/meta/data"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise MetaError(f"Failed to get meta-awareness data: {e}")
    
    def get_metrics(self) -> Dict[str, Any]:
        """
        Get meta-awareness metrics.
        
        Returns:
            Meta-awareness metrics dictionary
            
        Raises:
            MetaError: If getting meta-awareness metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/meta/metrics"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise MetaError(f"Failed to get meta-awareness metrics: {e}")
    
    def subscribe(self, event_type: str, callback: Callable[[Dict[str, Any]], None]) -> str:
        """
        Subscribe to meta-awareness events.
        
        Args:
            event_type: Type of events to subscribe to
            callback: Callback function for events
            
        Returns:
            Subscription ID string
            
        Raises:
            MetaError: If subscription fails
        """
        try:
            payload = {"event_type": event_type}
            
            response = self.client.session.post(
                f"{self.client.base_url}/meta/subscribe",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            subscription_id = result["subscription_id"]
            
            # Store subscription info
            self._callbacks[subscription_id] = {
                "event_type": event_type,
                "callback": callback
            }
            
            return subscription_id
            
        except Exception as e:
            raise MetaError(f"Failed to subscribe to meta-awareness events: {e}")
    
    def unsubscribe(self, subscription_id: str) -> bool:
        """
        Unsubscribe from meta-awareness events.
        
        Args:
            subscription_id: Subscription ID to remove
            
        Returns:
            True if unsubscription was successful
            
        Raises:
            MetaError: If unsubscription fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/meta/unsubscribe/{subscription_id}"
            )
            response.raise_for_status()
            
            # Remove subscription from local cache
            if subscription_id in self._callbacks:
                del self._callbacks[subscription_id]
            
            return True
            
        except Exception as e:
            raise MetaError(f"Failed to unsubscribe from meta-awareness events: {e}")
    
    def get_optimization_suggestions(self) -> List[Dict[str, Any]]:
        """
        Get optimization suggestions from meta-awareness.
        
        Returns:
            List of optimization suggestion dictionaries
            
        Raises:
            MetaError: If getting optimization suggestions fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/meta/optimization/suggestions"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise MetaError(f"Failed to get optimization suggestions: {e}")
    
    def apply_optimization(self, optimization_id: str) -> bool:
        """
        Apply an optimization suggestion.
        
        Args:
            optimization_id: Optimization ID to apply
            
        Returns:
            True if optimization was applied successfully
            
        Raises:
            MetaError: If optimization application fails
        """
        try:
            response = self.client.session.post(
                f"{self.client.base_url}/meta/optimization/apply/{optimization_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise MetaError(f"Failed to apply optimization: {e}")
    
    def get_health_status(self) -> Dict[str, Any]:
        """
        Get health status from meta-awareness.
        
        Returns:
            Health status dictionary
            
        Raises:
            MetaError: If getting health status fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/meta/health"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise MetaError(f"Failed to get health status: {e}")
    
    def trigger_self_healing(self, issue_type: str, issue_data: Dict[str, Any]) -> bool:
        """
        Trigger self-healing for a specific issue.
        
        Args:
            issue_type: Type of issue to heal
            issue_data: Issue data
            
        Returns:
            True if self-healing was triggered successfully
            
        Raises:
            MetaError: If self-healing trigger fails
        """
        try:
            payload = {
                "issue_type": issue_type,
                "issue_data": issue_data
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/meta/self-healing/trigger",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise MetaError(f"Failed to trigger self-healing: {e}")
    
    def get_self_healing_status(self) -> Dict[str, Any]:
        """
        Get self-healing status.
        
        Returns:
            Self-healing status dictionary
            
        Raises:
            MetaError: If getting self-healing status fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/meta/self-healing/status"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise MetaError(f"Failed to get self-healing status: {e}")
    
    @property
    def enabled(self) -> bool:
        """Check if meta-awareness is enabled."""
        return self._enabled

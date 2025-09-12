"""
Hologram client implementation.
"""

import os
from typing import Dict, Any, Optional, List
import requests
from .uor import UORManager
from .witness import WitnessManager
from .vpi import VPIManager
from .ctp96 import CTP96Manager
from .space import SpaceManager
from .meta import MetaManager
from .oracle import OracleManager
from .containers import ContainerManager
from .images import ImageManager
from .networks import NetworkManager
from .volumes import VolumeManager
from .errors import HologramError


class Client:
    """
    Hologram client with native support for UOR-IDs, witnesses, VPI leases, and CTP-96.
    
    This client provides first-class support for Hologram concepts while maintaining
    compatibility with standard container operations.
    """
    
    def __init__(
        self,
        base_url: Optional[str] = None,
        hologram_features: Optional[Dict[str, Any]] = None,
        timeout: Optional[int] = None,
        **kwargs
    ):
        """
        Initialize Hologram client.
        
        Args:
            base_url: Hologram daemon URL
            hologram_features: Hologram features configuration
            timeout: Request timeout
            **kwargs: Additional client options
        """
        # Get base URL from environment if not provided
        if base_url is None:
            base_url = os.getenv('HOLOGRAM_BASE_URL', 'http://localhost:2375')
        
        # Get Hologram features from environment if not provided
        if hologram_features is None:
            hologram_features = {
                'uor_id': os.getenv('HOLOGRAM_UOR_ID', 'true').lower() == 'true',
                'witness': os.getenv('HOLOGRAM_WITNESS', 'true').lower() == 'true',
                'vpi_lease': os.getenv('HOLOGRAM_VPI_LEASE', 'true').lower() == 'true',
                'ctp96': os.getenv('HOLOGRAM_CTP96', 'true').lower() == 'true',
                'space_12288': os.getenv('HOLOGRAM_SPACE_12288', 'true').lower() == 'true',
                'meta_awareness': os.getenv('HOLOGRAM_META_AWARENESS', 'false').lower() == 'true',
                'oracle': os.getenv('HOLOGRAM_ORACLE', 'false').lower() == 'true',
            }
        
        self.base_url = base_url
        self.hologram_features = hologram_features
        self.timeout = timeout or 30
        
        # Initialize HTTP session
        self.session = requests.Session()
        self.session.timeout = self.timeout
        
        # Initialize managers
        self._init_managers()
    
    def _init_managers(self) -> None:
        """Initialize Hologram managers."""
        # Core Hologram managers
        if self.hologram_features.get('uor_id'):
            self.uor = UORManager(self)
        else:
            self.uor = None
        
        if self.hologram_features.get('witness'):
            self.witness = WitnessManager(self)
        else:
            self.witness = None
        
        if self.hologram_features.get('vpi_lease'):
            self.vpi = VPIManager(self)
        else:
            self.vpi = None
        
        if self.hologram_features.get('ctp96'):
            self.ctp96 = CTP96Manager(self)
        else:
            self.ctp96 = None
        
        if self.hologram_features.get('space_12288'):
            self.space = SpaceManager(self)
        else:
            self.space = None
        
        if self.hologram_features.get('meta_awareness'):
            self.meta = MetaManager(self)
        else:
            self.meta = None
        
        if self.hologram_features.get('oracle'):
            self.oracle = OracleManager(self)
        else:
            self.oracle = None
        
        # Standard container managers
        self.containers = ContainerManager(self)
        self.images = ImageManager(self)
        self.networks = NetworkManager(self)
        self.volumes = VolumeManager(self)
    
    def ping(self) -> bool:
        """
        Ping the Hologram daemon.
        
        Returns:
            True if daemon is reachable, False otherwise
        """
        try:
            response = self.session.get(f"{self.base_url}/ping")
            return response.status_code == 200
        except Exception:
            return False
    
    def version(self) -> Dict[str, Any]:
        """
        Get Hologram daemon version information.
        
        Returns:
            Version information dictionary
        """
        try:
            response = self.session.get(f"{self.base_url}/version")
            response.raise_for_status()
            return response.json()
        except Exception as e:
            raise HologramError(f"Failed to get version: {e}")
    
    def info(self) -> Dict[str, Any]:
        """
        Get Hologram daemon information.
        
        Returns:
            Daemon information dictionary
        """
        try:
            response = self.session.get(f"{self.base_url}/info")
            response.raise_for_status()
            return response.json()
        except Exception as e:
            raise HologramError(f"Failed to get info: {e}")
    
    def close(self) -> None:
        """Close the client and cleanup resources."""
        if hasattr(self, 'session'):
            self.session.close()
    
    def __enter__(self):
        """Context manager entry."""
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()
    
    def __del__(self):
        """Destructor."""
        self.close()

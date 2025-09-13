"""
hologram: Native Hologram SDK with UOR-IDs, witnesses, VPI leases, and CTP-96.

This package provides first-class support for Hologram concepts including
UOR-IDs, witnesses, VPI leases, CTP-96 transport, and the 12,288 space.
"""

import os
from typing import Dict, Any, Optional

from .client import Client
from .uor import UORManager
from .witness import WitnessManager
from .vpi import VPIManager
from .ctp96 import CTP96Manager
from .space import SpaceManager
from .meta import MetaManager
from .oracle import OracleManager
from .errors import (
    HologramError,
    UORIDError,
    WitnessError,
    VPILeaseError,
    CTP96Error,
    SpaceError,
    MetaError,
    OracleError,
)

__version__ = "0.1.0"
__all__ = [
    "Client",
    "UORManager",
    "WitnessManager",
    "VPIManager",
    "CTP96Manager",
    "SpaceManager",
    "MetaManager",
    "OracleManager",
    "HologramError",
    "UORIDError",
    "WitnessError",
    "VPILeaseError",
    "CTP96Error",
    "SpaceError",
    "MetaError",
    "OracleError",
]


def create_client(
    base_url: Optional[str] = None,
    hologram_features: Optional[Dict[str, Any]] = None,
    **kwargs
) -> Client:
    """
    Create a Hologram client with specified features.
    
    Args:
        base_url: Hologram daemon URL
        hologram_features: Hologram features configuration
        **kwargs: Additional client options
        
    Returns:
        Client instance with specified features
        
    Environment Variables:
        HOLOGRAM_BASE_URL: Hologram daemon URL (default: http://localhost:2375)
        HOLOGRAM_UOR_ID: Enable UOR-ID support (default: true)
        HOLOGRAM_WITNESS: Enable witness verification (default: true)
        HOLOGRAM_VPI_LEASE: Enable VPI lease management (default: true)
        HOLOGRAM_CTP96: Enable CTP-96 transport (default: true)
        HOLOGRAM_SPACE_12288: Enable 12,288 space (default: true)
        HOLOGRAM_META_AWARENESS: Enable meta-awareness (default: false)
        HOLOGRAM_ORACLE: Enable oracle integration (default: false)
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
    
    return Client(
        base_url=base_url,
        hologram_features=hologram_features,
        **kwargs
    )


# Convenience function for quick client creation
def Client(
    base_url: Optional[str] = None,
    hologram_features: Optional[Dict[str, Any]] = None,
    **kwargs
) -> Client:
    """
    Create a Hologram client (alias for create_client).
    
    Args:
        base_url: Hologram daemon URL
        hologram_features: Hologram features configuration
        **kwargs: Additional client options
        
    Returns:
        Client instance with specified features
    """
    return create_client(base_url, hologram_features, **kwargs)

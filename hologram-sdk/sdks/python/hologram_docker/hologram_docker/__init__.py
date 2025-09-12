"""
hologram-docker: Drop-in Docker SDK replacement with Hologram features.

This package provides 100% compatibility with the standard docker Python package
while adding optional Hologram features like UOR-IDs, witnesses, VPI leases, and CTP-96.
"""

import os
from typing import Optional

from .client import DockerClient
from .api import APIClient
from .errors import DockerError, APIError, ContainerError, ImageNotFound, NotFound

__version__ = "0.1.0"
__all__ = [
    "DockerClient",
    "APIClient", 
    "DockerError",
    "APIError",
    "ContainerError",
    "ImageNotFound",
    "NotFound",
    "from_env",
    "DockerClient",
]


def from_env(
    use_ssh_client: bool = True,
    timeout: Optional[int] = None,
    version: Optional[str] = None,
    **kwargs
) -> DockerClient:
    """
    Create a Docker client from environment variables.
    
    This function provides 100% compatibility with docker.from_env() while
    adding optional Hologram features based on environment variables.
    
    Args:
        use_ssh_client: Whether to use SSH client for remote connections
        timeout: Timeout for API calls
        version: Docker API version to use
        **kwargs: Additional arguments passed to DockerClient
        
    Returns:
        DockerClient instance with optional Hologram features enabled
        
    Environment Variables:
        DOCKER_HOST: Docker daemon URL (default: unix:///var/run/docker.sock)
        DOCKER_TLS_VERIFY: Enable TLS verification (default: false)
        DOCKER_CERT_PATH: Path to TLS certificates (default: ~/.docker)
        HOLOGRAM_ENABLED: Enable Hologram features (default: false)
        HOLOGRAM_UOR_ID: Enable UOR-ID support (default: false)
        HOLOGRAM_WITNESS: Enable witness verification (default: false)
        HOLOGRAM_VPI_LEASE: Enable VPI lease management (default: false)
        HOLOGRAM_CTP96: Enable CTP-96 transport (default: false)
        HOLOGRAM_PROFILE: Set conformance profile (P-Core, P-Network, P-Runtime, P-Full)
    """
    # Get Docker host from environment
    import platform
    if platform.system() == "Windows":
        default_host = 'tcp://localhost:2375'
    else:
        default_host = 'unix:///var/run/docker.sock'
    docker_host = os.getenv('DOCKER_HOST', default_host)
    
    # Handle TLS configuration
    tls_verify = os.getenv('DOCKER_TLS_VERIFY', '').lower() in ('1', 'true', 'yes')
    tls_cert_path = os.getenv('DOCKER_CERT_PATH', os.path.expanduser('~/.docker'))
    
    # Configure TLS if needed
    tls_config = None
    if tls_verify and docker_host.startswith('tcp://'):
        try:
            import docker.tls
            tls_config = docker.tls.TLSConfig(
                client_cert=(os.path.join(tls_cert_path, 'cert.pem'),
                           os.path.join(tls_cert_path, 'key.pem')),
                ca_cert=os.path.join(tls_cert_path, 'ca.pem'),
                verify=True
            )
        except ImportError:
            # Fallback for older docker-py versions
            tls_config = True
    
    # Check for Hologram features
    hologram_enabled = os.getenv('HOLOGRAM_ENABLED', 'false').lower() == 'true'
    uor_id_enabled = os.getenv('HOLOGRAM_UOR_ID', 'false').lower() == 'true'
    witness_enabled = os.getenv('HOLOGRAM_WITNESS', 'false').lower() == 'true'
    vpi_lease_enabled = os.getenv('HOLOGRAM_VPI_LEASE', 'false').lower() == 'true'
    ctp96_enabled = os.getenv('HOLOGRAM_CTP96', 'false').lower() == 'true'
    profile = os.getenv('HOLOGRAM_PROFILE', 'P-Core')
    
    # Set Hologram features in kwargs
    if hologram_enabled or any([uor_id_enabled, witness_enabled, vpi_lease_enabled, ctp96_enabled]) or profile != 'P-Core':
        kwargs.setdefault('hologram_features', {
            'enabled': hologram_enabled,
            'uor_id': uor_id_enabled,
            'witness': witness_enabled,
            'vpi_lease': vpi_lease_enabled,
            'ctp96': ctp96_enabled,
            'profile': profile,
        })
    
    return DockerClient(
        base_url=docker_host,
        tls=tls_config,
        timeout=timeout,
        version=version,
        use_ssh_client=use_ssh_client,
        **kwargs
    )


# Re-export docker module for compatibility
import docker as _docker

# Monkey patch the docker module to use our client
_docker.from_env = from_env
_docker.DockerClient = DockerClient
_docker.APIClient = APIClient

# Re-export all docker symbols for compatibility
from docker import *  # noqa: F401, F403

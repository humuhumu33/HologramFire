"""
Docker client with Hologram features.
"""

import os
from typing import Dict, Any, Optional, Union, List
from docker import DockerClient as BaseDockerClient
from docker.models.containers import Container
from docker.models.images import Image
from docker.models.networks import Network
from docker.models.volumes import Volume

from .transport import APIClient
from .subsystems import Images, Containers, Networks, Volumes
from .hologram import HologramFeatures


class DockerClient(BaseDockerClient):
    """
    Docker client with optional Hologram features.
    
    This class extends the standard Docker client to add Hologram features
    while maintaining 100% compatibility with existing code.
    """
    
    def __init__(
        self,
        base_url: Optional[str] = None,
        version: Optional[str] = None,
        timeout: Optional[int] = None,
        tls: Optional[Any] = None,
        user_agent: Optional[str] = None,
        use_ssh_client: bool = True,
        max_pool_size: int = 10,
        **kwargs
    ):
        """
        Initialize Docker client with optional Hologram features.
        
        Args:
            base_url: Docker daemon URL
            version: Docker API version
            timeout: Request timeout
            tls: TLS configuration
            user_agent: User agent string
            use_ssh_client: Whether to use SSH client
            max_pool_size: Maximum connection pool size
            **kwargs: Additional arguments including hologram_features
        """
        # Extract Hologram features
        self.hologram_features = kwargs.pop('hologram_features', None)
        
        # Initialize base client
        super().__init__(
            base_url=base_url,
            version=version,
            timeout=timeout,
            tls=tls,
            user_agent=user_agent,
            use_ssh_client=use_ssh_client,
            max_pool_size=max_pool_size,
            **kwargs
        )
        
        # Initialize our custom API client
        self.api = APIClient(base_url=base_url, timeout=timeout)
        
        # Initialize Hologram features if enabled
        if self.hologram_features:
            self._hologram = HologramFeatures(self.api, self.hologram_features)
        else:
            self._hologram = None
    
    @classmethod
    def from_env(
        cls,
        use_ssh_client: bool = True,
        timeout: Optional[int] = None,
        version: Optional[str] = None,
        **kwargs
    ) -> 'DockerClient':
        """
        Create client from environment variables.
        
        Args:
            use_ssh_client: Whether to use SSH client
            timeout: Request timeout
            version: Docker API version
            **kwargs: Additional arguments
            
        Returns:
            DockerClient instance
        """
        # Check for Hologram features in environment
        hologram_features = None
        if os.getenv('HOLOGRAM_ENABLED', 'false').lower() == 'true':
            hologram_features = {
                'enabled': True,
                'uor_id': os.getenv('HOLOGRAM_UOR_ID', 'false').lower() == 'true',
                'witness': os.getenv('HOLOGRAM_WITNESS', 'false').lower() == 'true',
                'vpi_lease': os.getenv('HOLOGRAM_VPI_LEASE', 'false').lower() == 'true',
                'ctp96': os.getenv('HOLOGRAM_CTP96', 'false').lower() == 'true',
                'profile': os.getenv('HOLOGRAM_PROFILE', 'P-Core'),
            }
        
        if hologram_features:
            kwargs['hologram_features'] = hologram_features
        
        return cls(
            base_url=os.getenv('DOCKER_HOST'),
            version=version,
            timeout=timeout,
            use_ssh_client=use_ssh_client,
            **kwargs
        )
    
    def containers(self, **kwargs) -> Containers:
        """
        Get container collection with Hologram features.
        
        Returns:
            Containers instance
        """
        return Containers(self.api)
    
    def images(self, **kwargs) -> Images:
        """
        Get image collection with Hologram features.
        
        Returns:
            Images instance
        """
        return Images(self.api)
    
    def networks(self, **kwargs) -> Networks:
        """
        Get network collection with Hologram features.
        
        Returns:
            Networks instance
        """
        return Networks(self.api)
    
    def volumes(self, **kwargs) -> Volumes:
        """
        Get volume collection with Hologram features.
        
        Returns:
            Volumes instance
        """
        return Volumes(self.api)
    
    @property
    def hologram(self) -> Optional[HologramFeatures]:
        """
        Get Hologram features instance.
        
        Returns:
            HologramFeatures instance if enabled, None otherwise
        """
        return self._hologram


class ContainerCollection:
    """Container collection with Hologram features."""
    
    def __init__(self, client: DockerClient, **kwargs):
        self.client = client
        self.kwargs = kwargs
    
    def run(
        self,
        image: str,
        command: Optional[Union[str, List[str]]] = None,
        **kwargs
    ) -> Container:
        """
        Run a container with optional Hologram features.
        
        Args:
            image: Image name or ID
            command: Command to run
            **kwargs: Additional container options
            
        Returns:
            Container instance
        """
        # Check for Hologram labels
        labels = kwargs.get('labels', {})
        hologram_enabled = any(
            key.startswith('hologram.') for key in labels.keys()
        )
        
        # Add Hologram features if enabled
        if hologram_enabled and self.client._hologram:
            kwargs = self.client._hologram.enhance_container_run(image, **kwargs)
        
        # Run container using base client
        return self.client.api.containers.run(image, command, **kwargs)
    
    def create(self, image: str, **kwargs) -> Container:
        """
        Create a container with optional Hologram features.
        
        Args:
            image: Image name or ID
            **kwargs: Additional container options
            
        Returns:
            Container instance
        """
        # Check for Hologram labels
        labels = kwargs.get('labels', {})
        hologram_enabled = any(
            key.startswith('hologram.') for key in labels.keys()
        )
        
        # Add Hologram features if enabled
        if hologram_enabled and self.client._hologram:
            kwargs = self.client._hologram.enhance_container_create(image, **kwargs)
        
        # Create container using base client
        return self.client.api.containers.create(image, **kwargs)
    
    def get(self, container_id: str) -> Container:
        """Get container by ID."""
        return self.client.api.containers.get(container_id)
    
    def list(self, **kwargs) -> List[Container]:
        """List containers."""
        return self.client.api.containers.list(**kwargs)


class ImageCollection:
    """Image collection with Hologram features."""
    
    def __init__(self, client: DockerClient, **kwargs):
        self.client = client
        self.kwargs = kwargs
    
    def pull(self, repository: str, **kwargs) -> Image:
        """
        Pull an image with optional Hologram features.
        
        Args:
            repository: Image repository
            **kwargs: Additional pull options
            
        Returns:
            Image instance
        """
        # Add Hologram features if enabled
        if self.client._hologram:
            kwargs = self.client._hologram.enhance_image_pull(repository, **kwargs)
        
        # Pull image using base client
        return self.client.api.images.pull(repository, **kwargs)
    
    def get(self, image_id: str) -> Image:
        """Get image by ID."""
        return self.client.api.images.get(image_id)
    
    def list(self, **kwargs) -> List[Image]:
        """List images."""
        return self.client.api.images.list(**kwargs)


class NetworkCollection:
    """Network collection with Hologram features."""
    
    def __init__(self, client: DockerClient, **kwargs):
        self.client = client
        self.kwargs = kwargs
    
    def create(self, name: str, **kwargs) -> Network:
        """
        Create a network with optional Hologram features.
        
        Args:
            name: Network name
            **kwargs: Additional network options
            
        Returns:
            Network instance
        """
        # Add Hologram features if enabled
        if self.client._hologram:
            kwargs = self.client._hologram.enhance_network_create(name, **kwargs)
        
        # Create network using base client
        return self.client.api.networks.create(name, **kwargs)
    
    def get(self, network_id: str) -> Network:
        """Get network by ID."""
        return self.client.api.networks.get(network_id)
    
    def list(self, **kwargs) -> List[Network]:
        """List networks."""
        return self.client.api.networks.list(**kwargs)


class VolumeCollection:
    """Volume collection with Hologram features."""
    
    def __init__(self, client: DockerClient, **kwargs):
        self.client = client
        self.kwargs = kwargs
    
    def create(self, name: str, **kwargs) -> Volume:
        """
        Create a volume with optional Hologram features.
        
        Args:
            name: Volume name
            **kwargs: Additional volume options
            
        Returns:
            Volume instance
        """
        # Add Hologram features if enabled
        if self.client._hologram:
            kwargs = self.client._hologram.enhance_volume_create(name, **kwargs)
        
        # Create volume using base client
        return self.client.api.volumes.create(name, **kwargs)
    
    def get(self, volume_id: str) -> Volume:
        """Get volume by ID."""
        return self.client.api.volumes.get(volume_id)
    
    def list(self, **kwargs) -> List[Volume]:
        """List volumes."""
        return self.client.api.volumes.list(**kwargs)

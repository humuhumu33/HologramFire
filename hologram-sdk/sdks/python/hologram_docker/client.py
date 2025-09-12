"""
Docker-compatible client for Hologram SDK.

This module provides the main DockerClient class that mirrors docker-py's API
while adding optional Hologram features.
"""

import os
import urllib.parse
from typing import Optional, Dict, Any, List

from .api import APIClient
from .errors import DockerError


class DockerClient:
    """
    Docker-compatible client for Hologram SDK.
    
    This class provides the same interface as docker-py's DockerClient,
    but connects to hologramd instead of dockerd.
    """
    
    def __init__(
        self,
        base_url: Optional[str] = None,
        version: Optional[str] = None,
        timeout: int = 60,
        tls: bool = False,
        user_agent: str = "hologram-docker/0.1.0",
        use_ssh_client: bool = False,
        max_pool_size: int = 10,
        **kwargs
    ):
        """
        Initialize Docker client.
        
        Args:
            base_url: Base URL for Docker daemon (defaults to DOCKER_HOST or unix:///var/run/hologramd.sock)
            version: API version to use (defaults to '1.41')
            timeout: Timeout for requests in seconds
            tls: Enable TLS
            user_agent: User agent string
            use_ssh_client: Use SSH client for connection
            max_pool_size: Maximum pool size for connections
            **kwargs: Additional arguments passed to APIClient
        """
        if base_url is None:
            base_url = os.environ.get('DOCKER_HOST', 'unix:///var/run/hologramd.sock')
        
        if version is None:
            version = os.environ.get('DOCKER_API_VERSION', '1.41')
        
        # Parse base_url to determine connection type
        parsed = urllib.parse.urlparse(base_url)
        
        if parsed.scheme == 'unix':
            # UNIX socket connection
            self.api = APIClient(
                base_url=base_url,
                version=version,
                timeout=timeout,
                tls=False,  # TLS not applicable for UNIX sockets
                user_agent=user_agent,
                use_ssh_client=use_ssh_client,
                max_pool_size=max_pool_size,
                **kwargs
            )
        elif parsed.scheme in ('tcp', 'http', 'https'):
            # TCP connection
            self.api = APIClient(
                base_url=base_url,
                version=version,
                timeout=timeout,
                tls=tls or parsed.scheme == 'https',
                user_agent=user_agent,
                use_ssh_client=use_ssh_client,
                max_pool_size=max_pool_size,
                **kwargs
            )
        else:
            raise DockerError(f"Unsupported URL scheme: {parsed.scheme}")
        
        # Initialize sub-clients
        self.images = ImagesClient(self.api)
        self.containers = ContainersClient(self.api)
        self.networks = NetworksClient(self.api)
        self.volumes = VolumesClient(self.api)
        self.swarm = SwarmClient(self.api)
        
        # Hologram-specific clients (only available when features enabled)
        self._hologram_clients = {}
    
    def ping(self) -> Dict[str, Any]:
        """
        Ping the Docker daemon.
        
        Returns:
            Dict containing ping response
        """
        return self.api.ping()
    
    def version(self) -> Dict[str, Any]:
        """
        Get Docker daemon version information.
        
        Returns:
            Dict containing version information
        """
        return self.api.version()
    
    def info(self) -> Dict[str, Any]:
        """
        Get Docker daemon system information.
        
        Returns:
            Dict containing system information
        """
        return self.api.info()
    
    def close(self):
        """Close the client and clean up resources."""
        if hasattr(self.api, 'close'):
            self.api.close()
    
    def __enter__(self):
        """Context manager entry."""
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()
    
    # Hologram-specific methods (only available when features enabled)
    
    def enable_hologram_features(self, features: List[str]):
        """
        Enable Hologram features.
        
        Args:
            features: List of feature names to enable
        """
        # This would be implemented to enable specific Hologram features
        # For now, it's a placeholder
        pass
    
    def get_hologram_info(self) -> Dict[str, Any]:
        """
        Get Hologram-specific information.
        
        Returns:
            Dict containing Hologram information
        """
        # This would return Hologram-specific information
        # For now, it's a placeholder
        return {}


class ImagesClient:
    """Client for Docker images operations."""
    
    def __init__(self, api: APIClient):
        self.api = api
    
    def list(self, name: Optional[str] = None, all: bool = False, 
             filters: Optional[Dict[str, Any]] = None, 
             verbose: bool = False) -> List[Dict[str, Any]]:
        """
        List Docker images.
        
        Args:
            name: Filter by image name
            all: Show all images (including intermediate)
            filters: Filter options
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            List of image dictionaries
        """
        params = {}
        if name:
            params['name'] = name
        if all:
            params['all'] = 'true'
        if filters:
            params['filters'] = filters
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get('/images/json', params=params)
    
    def pull(self, repository: str, tag: Optional[str] = None, 
             stream: bool = False, **kwargs) -> Any:
        """
        Pull an image from a registry.
        
        Args:
            repository: Repository name
            tag: Tag name (defaults to 'latest')
            stream: Stream the response
            **kwargs: Additional arguments
            
        Returns:
            Image pull result
        """
        if tag is None:
            tag = 'latest'
        
        params = {
            'fromImage': repository,
            'tag': tag,
        }
        
        # Add Hologram-specific parameters
        if kwargs.get('verbose'):
            params['verbose'] = 'true'
        
        if stream:
            return self.api.post('/images/create', params=params, stream=True)
        else:
            return self.api.post('/images/create', params=params)
    
    def push(self, repository: str, tag: Optional[str] = None, 
             stream: bool = False, **kwargs) -> Any:
        """
        Push an image to a registry.
        
        Args:
            repository: Repository name
            tag: Tag name (defaults to 'latest')
            stream: Stream the response
            **kwargs: Additional arguments
            
        Returns:
            Image push result
        """
        if tag is None:
            tag = 'latest'
        
        params = {
            'tag': f"{repository}:{tag}"
        }
        
        if stream:
            return self.api.post(f'/images/{repository}/push', params=params, stream=True)
        else:
            return self.api.post(f'/images/{repository}/push', params=params)
    
    def remove(self, image: str, force: bool = False, 
               noprune: bool = False) -> List[Dict[str, Any]]:
        """
        Remove an image.
        
        Args:
            image: Image ID or name
            force: Force removal
            noprune: Don't delete untagged parents
            
        Returns:
            List of removal results
        """
        params = {}
        if force:
            params['force'] = 'true'
        if noprune:
            params['noprune'] = 'true'
        
        return self.api.delete(f'/images/{image}', params=params)
    
    def inspect(self, image: str, verbose: bool = False) -> Dict[str, Any]:
        """
        Inspect an image.
        
        Args:
            image: Image ID or name
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            Image inspection result
        """
        params = {}
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get(f'/images/{image}/json', params=params)


class ContainersClient:
    """Client for Docker containers operations."""
    
    def __init__(self, api: APIClient):
        self.api = api
    
    def list(self, all: bool = False, since: Optional[str] = None,
             before: Optional[str] = None, limit: Optional[int] = None,
             size: bool = False, filters: Optional[Dict[str, Any]] = None,
             verbose: bool = False) -> List[Dict[str, Any]]:
        """
        List Docker containers.
        
        Args:
            all: Show all containers (including stopped)
            since: Show containers created since this container
            before: Show containers created before this container
            limit: Limit number of containers
            size: Show container sizes
            filters: Filter options
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            List of container dictionaries
        """
        params = {}
        if all:
            params['all'] = 'true'
        if since:
            params['since'] = since
        if before:
            params['before'] = before
        if limit:
            params['limit'] = limit
        if size:
            params['size'] = 'true'
        if filters:
            params['filters'] = filters
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get('/containers/json', params=params)
    
    def create(self, image: str, command: Optional[str] = None,
               **kwargs) -> Dict[str, Any]:
        """
        Create a container.
        
        Args:
            image: Image to use
            command: Command to run
            **kwargs: Additional container configuration
            
        Returns:
            Container creation result
        """
        config = {
            'Image': image,
        }
        
        if command:
            config['Cmd'] = command
        
        # Add additional configuration
        config.update(kwargs)
        
        return self.api.post('/containers/create', json=config)
    
    def start(self, container: str, **kwargs) -> None:
        """
        Start a container.
        
        Args:
            container: Container ID or name
            **kwargs: Additional start options
        """
        self.api.post(f'/containers/{container}/start', json=kwargs)
    
    def stop(self, container: str, timeout: int = 10) -> None:
        """
        Stop a container.
        
        Args:
            container: Container ID or name
            timeout: Timeout in seconds
        """
        params = {'t': timeout}
        self.api.post(f'/containers/{container}/stop', params=params)
    
    def remove(self, container: str, force: bool = False, 
               v: bool = False) -> None:
        """
        Remove a container.
        
        Args:
            container: Container ID or name
            force: Force removal
            v: Remove associated volumes
        """
        params = {}
        if force:
            params['force'] = 'true'
        if v:
            params['v'] = 'true'
        
        self.api.delete(f'/containers/{container}', params=params)
    
    def inspect(self, container: str, verbose: bool = False) -> Dict[str, Any]:
        """
        Inspect a container.
        
        Args:
            container: Container ID or name
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            Container inspection result
        """
        params = {}
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get(f'/containers/{container}/json', params=params)
    
    def logs(self, container: str, stdout: bool = True, stderr: bool = True,
             stream: bool = False, timestamps: bool = False,
             tail: Optional[str] = None, since: Optional[str] = None,
             follow: bool = False) -> Any:
        """
        Get container logs.
        
        Args:
            container: Container ID or name
            stdout: Include stdout
            stderr: Include stderr
            stream: Stream the response
            timestamps: Include timestamps
            tail: Number of lines to show
            since: Show logs since timestamp
            follow: Follow log output
            
        Returns:
            Container logs
        """
        params = {}
        if stdout:
            params['stdout'] = 'true'
        if stderr:
            params['stderr'] = 'true'
        if timestamps:
            params['timestamps'] = 'true'
        if tail:
            params['tail'] = tail
        if since:
            params['since'] = since
        if follow:
            params['follow'] = 'true'
        
        if stream:
            return self.api.get(f'/containers/{container}/logs', params=params, stream=True)
        else:
            return self.api.get(f'/containers/{container}/logs', params=params)


class NetworksClient:
    """Client for Docker networks operations."""
    
    def __init__(self, api: APIClient):
        self.api = api
    
    def list(self, filters: Optional[Dict[str, Any]] = None,
             verbose: bool = False) -> List[Dict[str, Any]]:
        """
        List Docker networks.
        
        Args:
            filters: Filter options
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            List of network dictionaries
        """
        params = {}
        if filters:
            params['filters'] = filters
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get('/networks', params=params)
    
    def create(self, name: str, driver: str = 'bridge', **kwargs) -> Dict[str, Any]:
        """
        Create a network.
        
        Args:
            name: Network name
            driver: Network driver
            **kwargs: Additional network configuration
            
        Returns:
            Network creation result
        """
        config = {
            'Name': name,
            'Driver': driver,
        }
        config.update(kwargs)
        
        return self.api.post('/networks/create', json=config)
    
    def remove(self, network: str) -> None:
        """
        Remove a network.
        
        Args:
            network: Network ID or name
        """
        self.api.delete(f'/networks/{network}')
    
    def inspect(self, network: str, verbose: bool = False) -> Dict[str, Any]:
        """
        Inspect a network.
        
        Args:
            network: Network ID or name
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            Network inspection result
        """
        params = {}
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get(f'/networks/{network}', params=params)


class VolumesClient:
    """Client for Docker volumes operations."""
    
    def __init__(self, api: APIClient):
        self.api = api
    
    def list(self, filters: Optional[Dict[str, Any]] = None,
             verbose: bool = False) -> Dict[str, Any]:
        """
        List Docker volumes.
        
        Args:
            filters: Filter options
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            Volume list result
        """
        params = {}
        if filters:
            params['filters'] = filters
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get('/volumes', params=params)
    
    def create(self, name: str, driver: str = 'local', **kwargs) -> Dict[str, Any]:
        """
        Create a volume.
        
        Args:
            name: Volume name
            driver: Volume driver
            **kwargs: Additional volume configuration
            
        Returns:
            Volume creation result
        """
        config = {
            'Name': name,
            'Driver': driver,
        }
        config.update(kwargs)
        
        return self.api.post('/volumes/create', json=config)
    
    def remove(self, volume: str, force: bool = False) -> None:
        """
        Remove a volume.
        
        Args:
            volume: Volume ID or name
            force: Force removal
        """
        params = {}
        if force:
            params['force'] = 'true'
        
        self.api.delete(f'/volumes/{volume}', params=params)
    
    def inspect(self, volume: str, verbose: bool = False) -> Dict[str, Any]:
        """
        Inspect a volume.
        
        Args:
            volume: Volume ID or name
            verbose: Include Hologram extensions (XHologram fields)
            
        Returns:
            Volume inspection result
        """
        params = {}
        if verbose:
            params['verbose'] = 'true'
        
        return self.api.get(f'/volumes/{volume}', params=params)


class SwarmClient:
    """Client for Docker Swarm operations."""
    
    def __init__(self, api: APIClient):
        self.api = api
    
    def init(self, **kwargs) -> str:
        """
        Initialize a swarm.
        
        Args:
            **kwargs: Swarm configuration
            
        Returns:
            Swarm token
        """
        return self.api.post('/swarm/init', json=kwargs)
    
    def join(self, **kwargs) -> None:
        """
        Join a swarm.
        
        Args:
            **kwargs: Join configuration
        """
        self.api.post('/swarm/join', json=kwargs)
    
    def leave(self, force: bool = False) -> None:
        """
        Leave a swarm.
        
        Args:
            force: Force leave
        """
        params = {}
        if force:
            params['force'] = 'true'
        
        self.api.post('/swarm/leave', params=params)
    
    def inspect(self) -> Dict[str, Any]:
        """
        Inspect swarm.
        
        Returns:
            Swarm inspection result
        """
        return self.api.get('/swarm')


# Convenience function for creating a client
def from_env(**kwargs) -> DockerClient:
    """
    Create a Docker client from environment variables.
    
    Args:
        **kwargs: Additional arguments passed to DockerClient
        
    Returns:
        DockerClient instance
    """
    return DockerClient(**kwargs)

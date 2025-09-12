"""
Subsystems for hologram-docker (images, containers, etc.).
"""

from typing import List, Dict, Any, Optional, Union
from .transport import APIClient


class Images:
    """
    Images subsystem for hologram-docker.
    
    Provides the same interface as docker-py's Images class.
    """
    
    def __init__(self, api: APIClient):
        """
        Initialize images subsystem.
        
        Args:
            api: API client instance
        """
        self.api = api
    
    def list(self, **params) -> List[Dict[str, Any]]:
        """
        List images.
        
        Args:
            **params: Additional parameters (all, filters, etc.)
            
        Returns:
            List of image information dictionaries
        """
        response = self.api.get("/images/json", params=params)
        response.raise_for_status()
        return response.json()
    
    def get(self, image_id: str) -> Dict[str, Any]:
        """
        Get image information.
        
        Args:
            image_id: Image ID
            
        Returns:
            Image information dictionary
        """
        response = self.api.get(f"/images/{image_id}/json")
        response.raise_for_status()
        return response.json()
    
    def pull(self, repository: str, tag: Optional[str] = None, stream: bool = False, **kwargs) -> Union[str, Dict[str, Any]]:
        """
        Pull an image.
        
        Args:
            repository: Image repository
            tag: Image tag
            stream: Whether to stream progress events
            **kwargs: Additional pull options
            
        Returns:
            Pull response or generator of progress events
        """
        params = {"fromImage": repository}
        if tag:
            params["tag"] = tag
        
        response = self.api.post("/images/create", params=params, stream=stream, **kwargs)
        response.raise_for_status()
        
        if stream:
            # Return a generator that yields progress events
            return self._parse_pull_stream(response)
        else:
            # Return the response text for non-streaming
            return response.text
    
    def _parse_pull_stream(self, response):
        """
        Parse streaming pull response into progress events.
        
        Args:
            response: Streaming response object
            
        Yields:
            Progress event dictionaries
        """
        import json
        
        for line in response.iter_lines():
            if line:
                try:
                    # Each line is a JSON object
                    event = json.loads(line.decode('utf-8'))
                    yield event
                except json.JSONDecodeError:
                    # Skip malformed lines
                    continue
    
    def push(self, repository: str, tag: Optional[str] = None, **kwargs) -> Union[str, Dict[str, Any]]:
        """
        Push an image.
        
        Args:
            repository: Image repository
            tag: Image tag
            **kwargs: Additional push options
            
        Returns:
            Push response
        """
        params = {}
        if tag:
            params["tag"] = tag
        
        response = self.api.post(f"/images/{repository}/push", params=params, **kwargs)
        response.raise_for_status()
        
        # Return the response text for streaming
        return response.text
    
    def remove(self, image_id: str, force: bool = False, noprune: bool = False) -> List[Dict[str, Any]]:
        """
        Remove an image.
        
        Args:
            image_id: Image ID to remove
            force: Whether to force removal
            noprune: Whether to skip pruning
            
        Returns:
            List of removal results
        """
        params = {"force": force, "noprune": noprune}
        
        response = self.api.delete(f"/images/{image_id}", params=params)
        response.raise_for_status()
        return response.json()
    
    def tag(self, image_id: str, repository: str, tag: Optional[str] = None, force: bool = False) -> bool:
        """
        Tag an image.
        
        Args:
            image_id: Image ID to tag
            repository: Repository name
            tag: Tag name
            force: Whether to force tagging
            
        Returns:
            True if successful
        """
        params = {"repo": repository, "force": force}
        if tag:
            params["tag"] = tag
        
        response = self.api.post(f"/images/{image_id}/tag", params=params)
        response.raise_for_status()
        return True
    
    def build(self, path: str, **kwargs) -> Union[str, Dict[str, Any]]:
        """
        Build an image.
        
        Args:
            path: Build context path
            **kwargs: Additional build options
            
        Returns:
            Build response
        """
        # This is a simplified implementation
        # In a real implementation, you'd handle the build context
        response = self.api.post("/build", **kwargs)
        response.raise_for_status()
        
        # Return the response text for streaming
        return response.text
    
    def search(self, term: str, **kwargs) -> List[Dict[str, Any]]:
        """
        Search images.
        
        Args:
            term: Search term
            **kwargs: Additional search options
            
        Returns:
            List of search results
        """
        params = {"term": term}
        params.update(kwargs)
        
        response = self.api.get("/images/search", params=params)
        response.raise_for_status()
        return response.json()
    
    def history(self, image_id: str) -> List[Dict[str, Any]]:
        """
        Get image history.
        
        Args:
            image_id: Image ID
            
        Returns:
            List of history entries
        """
        response = self.api.get(f"/images/{image_id}/history")
        response.raise_for_status()
        return response.json()


class Containers:
    """
    Containers subsystem for hologram-docker.
    
    Provides the same interface as docker-py's Containers class.
    """
    
    def __init__(self, api: APIClient):
        """
        Initialize containers subsystem.
        
        Args:
            api: API client instance
        """
        self.api = api
    
    def list(self, **params) -> List[Dict[str, Any]]:
        """
        List containers.
        
        Args:
            **params: Additional parameters (all, filters, etc.)
            
        Returns:
            List of container information dictionaries
        """
        response = self.api.get("/containers/json", params=params)
        response.raise_for_status()
        return response.json()
    
    def get(self, container_id: str) -> Dict[str, Any]:
        """
        Get container information.
        
        Args:
            container_id: Container ID
            
        Returns:
            Container information dictionary
        """
        response = self.api.get(f"/containers/{container_id}/json")
        response.raise_for_status()
        return response.json()
    
    def create(self, image: str, **kwargs) -> Dict[str, Any]:
        """
        Create a container.
        
        Args:
            image: Image name
            **kwargs: Additional container options
            
        Returns:
            Container creation response
        """
        payload = {
            "Image": image,
            **kwargs
        }
        
        response = self.api.post("/containers/create", json=payload)
        response.raise_for_status()
        return response.json()
    
    def start(self, container_id: str, **kwargs) -> bool:
        """
        Start a container.
        
        Args:
            container_id: Container ID
            **kwargs: Additional start options
            
        Returns:
            True if successful
        """
        response = self.api.post(f"/containers/{container_id}/start", **kwargs)
        response.raise_for_status()
        return True
    
    def stop(self, container_id: str, timeout: Optional[int] = None) -> bool:
        """
        Stop a container.
        
        Args:
            container_id: Container ID
            timeout: Stop timeout
            
        Returns:
            True if successful
        """
        params = {}
        if timeout is not None:
            params["t"] = timeout
        
        response = self.api.post(f"/containers/{container_id}/stop", params=params)
        response.raise_for_status()
        return True
    
    def remove(self, container_id: str, force: bool = False, v: bool = False) -> bool:
        """
        Remove a container.
        
        Args:
            container_id: Container ID
            force: Whether to force removal
            v: Whether to remove volumes
            
        Returns:
            True if successful
        """
        params = {"force": force, "v": v}
        
        response = self.api.delete(f"/containers/{container_id}", params=params)
        response.raise_for_status()
        return True
    
    def logs(self, container_id: str, **kwargs) -> str:
        """
        Get container logs.
        
        Args:
            container_id: Container ID
            **kwargs: Additional log options
            
        Returns:
            Container logs
        """
        response = self.api.get(f"/containers/{container_id}/logs", params=kwargs)
        response.raise_for_status()
        return response.text
    
    def exec(self, container_id: str, command: Union[str, List[str]], **kwargs) -> Dict[str, Any]:
        """
        Execute a command in a container.
        
        Args:
            container_id: Container ID
            command: Command to execute
            **kwargs: Additional exec options
            
        Returns:
            Execution response
        """
        payload = {
            "Cmd": command if isinstance(command, list) else [command],
            **kwargs
        }
        
        response = self.api.post(f"/containers/{container_id}/exec", json=payload)
        response.raise_for_status()
        return response.json()


class Networks:
    """
    Networks subsystem for hologram-docker.
    
    Provides the same interface as docker-py's Networks class.
    """
    
    def __init__(self, api: APIClient):
        """
        Initialize networks subsystem.
        
        Args:
            api: API client instance
        """
        self.api = api
    
    def list(self, **params) -> List[Dict[str, Any]]:
        """
        List networks.
        
        Args:
            **params: Additional parameters (filters, etc.)
            
        Returns:
            List of network information dictionaries
        """
        response = self.api.get("/networks", params=params)
        response.raise_for_status()
        return response.json()
    
    def get(self, network_id: str) -> Dict[str, Any]:
        """
        Get network information.
        
        Args:
            network_id: Network ID
            
        Returns:
            Network information dictionary
        """
        response = self.api.get(f"/networks/{network_id}")
        response.raise_for_status()
        return response.json()
    
    def create(self, name: str, **kwargs) -> Dict[str, Any]:
        """
        Create a network.
        
        Args:
            name: Network name
            **kwargs: Additional network options
            
        Returns:
            Network creation response
        """
        payload = {
            "Name": name,
            **kwargs
        }
        
        response = self.api.post("/networks/create", json=payload)
        response.raise_for_status()
        return response.json()
    
    def remove(self, network_id: str) -> bool:
        """
        Remove a network.
        
        Args:
            network_id: Network ID
            
        Returns:
            True if successful
        """
        response = self.api.delete(f"/networks/{network_id}")
        response.raise_for_status()
        return True


class Volumes:
    """
    Volumes subsystem for hologram-docker.
    
    Provides the same interface as docker-py's Volumes class.
    """
    
    def __init__(self, api: APIClient):
        """
        Initialize volumes subsystem.
        
        Args:
            api: API client instance
        """
        self.api = api
    
    def list(self, **params) -> Dict[str, Any]:
        """
        List volumes.
        
        Args:
            **params: Additional parameters (filters, etc.)
            
        Returns:
            Volumes information dictionary
        """
        response = self.api.get("/volumes", params=params)
        response.raise_for_status()
        return response.json()
    
    def get(self, volume_id: str) -> Dict[str, Any]:
        """
        Get volume information.
        
        Args:
            volume_id: Volume ID
            
        Returns:
            Volume information dictionary
        """
        response = self.api.get(f"/volumes/{volume_id}")
        response.raise_for_status()
        return response.json()
    
    def create(self, name: str, **kwargs) -> Dict[str, Any]:
        """
        Create a volume.
        
        Args:
            name: Volume name
            **kwargs: Additional volume options
            
        Returns:
            Volume creation response
        """
        payload = {
            "Name": name,
            **kwargs
        }
        
        response = self.api.post("/volumes/create", json=payload)
        response.raise_for_status()
        return response.json()
    
    def remove(self, volume_id: str, force: bool = False) -> bool:
        """
        Remove a volume.
        
        Args:
            volume_id: Volume ID
            force: Whether to force removal
            
        Returns:
            True if successful
        """
        params = {"force": force}
        
        response = self.api.delete(f"/volumes/{volume_id}", params=params)
        response.raise_for_status()
        return True

"""
Image manager for native Hologram SDK.
"""

from typing import Dict, Any, Optional, List
from .client import Client
from .errors import ImageError


class ImageManager:
    """
    Image manager with native Hologram support.
    
    This manager provides image operations with first-class support for
    UOR-IDs, witnesses, and Hologram-specific features.
    """
    
    def __init__(self, client: Client):
        """
        Initialize image manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def pull(
        self,
        repository: str,
        tag: Optional[str] = None,
        uor_id: Optional[str] = None,
        witness: Optional[str] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Pull an image with Hologram features.
        
        Args:
            repository: Image repository
            tag: Image tag
            uor_id: Optional UOR-ID for the image
            witness: Optional witness for verification
            **kwargs: Additional pull options
            
        Returns:
            Pull response dictionary
            
        Raises:
            ImageError: If image pull fails
        """
        try:
            payload = {
                "repository": repository,
                "tag": tag,
                "uor_id": uor_id,
                "witness": witness,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/images/pull",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to pull image: {e}")
    
    def push(
        self,
        repository: str,
        tag: Optional[str] = None,
        uor_id: Optional[str] = None,
        witness: Optional[str] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Push an image with Hologram features.
        
        Args:
            repository: Image repository
            tag: Image tag
            uor_id: Optional UOR-ID for the image
            witness: Optional witness for verification
            **kwargs: Additional push options
            
        Returns:
            Push response dictionary
            
        Raises:
            ImageError: If image push fails
        """
        try:
            payload = {
                "repository": repository,
                "tag": tag,
                "uor_id": uor_id,
                "witness": witness,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/images/push",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to push image: {e}")
    
    def build(
        self,
        path: str,
        tag: Optional[str] = None,
        uor_id: Optional[str] = None,
        witness: Optional[str] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Build an image with Hologram features.
        
        Args:
            path: Build context path
            tag: Image tag
            uor_id: Optional UOR-ID for the image
            witness: Optional witness for verification
            **kwargs: Additional build options
            
        Returns:
            Build response dictionary
            
        Raises:
            ImageError: If image build fails
        """
        try:
            payload = {
                "path": path,
                "tag": tag,
                "uor_id": uor_id,
                "witness": witness,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/images/build",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to build image: {e}")
    
    def list(self, all: bool = False, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List images.
        
        Args:
            all: Whether to include intermediate images
            limit: Maximum number of images to return
            offset: Number of images to skip
            
        Returns:
            List of image information dictionaries
            
        Raises:
            ImageError: If listing images fails
        """
        try:
            params = {"all": all}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/images/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to list images: {e}")
    
    def get_info(self, image_id: str) -> Dict[str, Any]:
        """
        Get image information.
        
        Args:
            image_id: Image ID to get information for
            
        Returns:
            Image information dictionary
            
        Raises:
            ImageError: If getting image info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/images/info/{image_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to get image info for {image_id}: {e}")
    
    def remove(self, image_id: str, force: bool = False) -> bool:
        """
        Remove an image.
        
        Args:
            image_id: Image ID to remove
            force: Whether to force removal
            
        Returns:
            True if removal was successful
            
        Raises:
            ImageError: If image removal fails
        """
        try:
            params = {"force": force}
            
            response = self.client.session.delete(
                f"{self.client.base_url}/images/remove/{image_id}",
                params=params
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ImageError(f"Failed to remove image {image_id}: {e}")
    
    def tag(self, image_id: str, repository: str, tag: Optional[str] = None) -> bool:
        """
        Tag an image.
        
        Args:
            image_id: Image ID to tag
            repository: Repository name
            tag: Tag name
            
        Returns:
            True if tagging was successful
            
        Raises:
            ImageError: If image tagging fails
        """
        try:
            payload = {
                "repository": repository,
                "tag": tag
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/images/tag/{image_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ImageError(f"Failed to tag image {image_id}: {e}")
    
    def get_hologram_info(self, image_id: str) -> Dict[str, Any]:
        """
        Get Hologram-specific information for an image.
        
        Args:
            image_id: Image ID to get Hologram info for
            
        Returns:
            Hologram information dictionary
            
        Raises:
            ImageError: If getting Hologram info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/images/hologram/{image_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to get Hologram info for image {image_id}: {e}")
    
    def update_hologram_config(self, image_id: str, config: Dict[str, Any]) -> bool:
        """
        Update Hologram configuration for an image.
        
        Args:
            image_id: Image ID to update
            config: New Hologram configuration
            
        Returns:
            True if update was successful
            
        Raises:
            ImageError: If Hologram config update fails
        """
        try:
            payload = {"config": config}
            
            response = self.client.session.put(
                f"{self.client.base_url}/images/hologram/{image_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise ImageError(f"Failed to update Hologram config for image {image_id}: {e}")
    
    def search(self, query: str, limit: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        Search images by query.
        
        Args:
            query: Search query
            limit: Maximum number of results to return
            
        Returns:
            List of matching image information dictionaries
            
        Raises:
            ImageError: If image search fails
        """
        try:
            params = {"query": query}
            if limit is not None:
                params["limit"] = limit
            
            response = self.client.session.get(
                f"{self.client.base_url}/images/search",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to search images: {e}")
    
    def get_history(self, image_id: str) -> List[Dict[str, Any]]:
        """
        Get image history.
        
        Args:
            image_id: Image ID to get history for
            
        Returns:
            List of image history entries
            
        Raises:
            ImageError: If getting image history fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/images/history/{image_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise ImageError(f"Failed to get history for image {image_id}: {e}")

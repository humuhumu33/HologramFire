"""
12,288 space manager.
"""

from typing import Dict, Any, Optional, List, Tuple
from .client import Client
from .errors import SpaceError


class SpaceManager:
    """
    12,288 space manager for high-dimensional coordinate system operations.
    
    The 12,288 space provides a high-dimensional coordinate system for object
    placement and spatial queries.
    """
    
    def __init__(self, client: Client):
        """
        Initialize space manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
        self.dimensions = 12288
    
    def create_coordinate(self, dimensions: int = 12288, values: Optional[List[float]] = None) -> Dict[str, Any]:
        """
        Create a coordinate in 12,288 space.
        
        Args:
            dimensions: Number of dimensions (default: 12288)
            values: Optional coordinate values
            
        Returns:
            Coordinate information dictionary
            
        Raises:
            SpaceError: If coordinate creation fails
        """
        try:
            if dimensions != self.dimensions:
                raise SpaceError(f"Invalid dimensions: {dimensions}. Must be {self.dimensions}")
            
            payload = {
                "dimensions": dimensions,
                "values": values or []
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/space/coordinate/create",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to create coordinate: {e}")
    
    def place(self, uor_id: str, coordinate: Dict[str, Any], metadata: Optional[Dict[str, Any]] = None) -> str:
        """
        Place an object in 12,288 space.
        
        Args:
            uor_id: UOR-ID of object to place
            coordinate: Coordinate to place object at
            metadata: Optional metadata for placement
            
        Returns:
            Placement ID string
            
        Raises:
            SpaceError: If object placement fails
        """
        try:
            payload = {
                "uor_id": uor_id,
                "coordinate": coordinate,
                "metadata": metadata or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/space/place",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["placement_id"]
            
        except Exception as e:
            raise SpaceError(f"Failed to place object in space: {e}")
    
    def query(self, coordinate: Dict[str, Any], radius: float, limit: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        Query objects in 12,288 space within a radius.
        
        Args:
            coordinate: Center coordinate for query
            radius: Search radius
            limit: Maximum number of results to return
            
        Returns:
            List of object information dictionaries
            
        Raises:
            SpaceError: If space query fails
        """
        try:
            params = {
                "coordinate": coordinate,
                "radius": radius
            }
            if limit is not None:
                params["limit"] = limit
            
            response = self.client.session.get(
                f"{self.client.base_url}/space/query",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to query space: {e}")
    
    def move(self, placement_id: str, new_coordinate: Dict[str, Any]) -> bool:
        """
        Move an object to a new coordinate in 12,288 space.
        
        Args:
            placement_id: Placement ID to move
            new_coordinate: New coordinate for object
            
        Returns:
            True if move was successful
            
        Raises:
            SpaceError: If object move fails
        """
        try:
            payload = {
                "placement_id": placement_id,
                "new_coordinate": new_coordinate
            }
            
            response = self.client.session.put(
                f"{self.client.base_url}/space/move/{placement_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise SpaceError(f"Failed to move object in space: {e}")
    
    def remove(self, placement_id: str) -> bool:
        """
        Remove an object from 12,288 space.
        
        Args:
            placement_id: Placement ID to remove
            
        Returns:
            True if removal was successful
            
        Raises:
            SpaceError: If object removal fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/space/remove/{placement_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise SpaceError(f"Failed to remove object from space: {e}")
    
    def get_placement_info(self, placement_id: str) -> Dict[str, Any]:
        """
        Get placement information.
        
        Args:
            placement_id: Placement ID to get information for
            
        Returns:
            Placement information dictionary
            
        Raises:
            SpaceError: If getting placement info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/space/placement/{placement_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to get placement info for {placement_id}: {e}")
    
    def list_placements(self, uor_id: Optional[str] = None, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List object placements in 12,288 space.
        
        Args:
            uor_id: Optional UOR-ID to filter placements by
            limit: Maximum number of placements to return
            offset: Number of placements to skip
            
        Returns:
            List of placement information dictionaries
            
        Raises:
            SpaceError: If listing placements fails
        """
        try:
            params = {}
            if uor_id is not None:
                params["uor_id"] = uor_id
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/space/placements",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to list placements: {e}")
    
    def create_region(self, center_coordinate: Dict[str, Any], radius: float, region_config: Optional[Dict[str, Any]] = None) -> str:
        """
        Create a region in 12,288 space.
        
        Args:
            center_coordinate: Center coordinate of region
            radius: Radius of region
            region_config: Optional region configuration
            
        Returns:
            Region ID string
            
        Raises:
            SpaceError: If region creation fails
        """
        try:
            payload = {
                "center_coordinate": center_coordinate,
                "radius": radius,
                "region_config": region_config or {}
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/space/region/create",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["region_id"]
            
        except Exception as e:
            raise SpaceError(f"Failed to create region: {e}")
    
    def get_region_info(self, region_id: str) -> Dict[str, Any]:
        """
        Get region information.
        
        Args:
            region_id: Region ID to get information for
            
        Returns:
            Region information dictionary
            
        Raises:
            SpaceError: If getting region info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/space/region/{region_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to get region info for {region_id}: {e}")
    
    def list_regions(self, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List regions in 12,288 space.
        
        Args:
            limit: Maximum number of regions to return
            offset: Number of regions to skip
            
        Returns:
            List of region information dictionaries
            
        Raises:
            SpaceError: If listing regions fails
        """
        try:
            params = {}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/space/regions",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to list regions: {e}")
    
    def delete_region(self, region_id: str) -> bool:
        """
        Delete a region from 12,288 space.
        
        Args:
            region_id: Region ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            SpaceError: If region deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/space/region/delete/{region_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise SpaceError(f"Failed to delete region {region_id}: {e}")
    
    def get_space_metrics(self) -> Dict[str, Any]:
        """
        Get 12,288 space metrics.
        
        Returns:
            Space metrics dictionary
            
        Raises:
            SpaceError: If getting space metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/space/metrics"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise SpaceError(f"Failed to get space metrics: {e}")

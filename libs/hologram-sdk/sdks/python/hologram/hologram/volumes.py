"""
Volume manager for native Hologram SDK.
"""

from typing import Dict, Any, Optional, List
from .client import Client
from .errors import VolumeError


class VolumeManager:
    """
    Volume manager with native Hologram support.
    
    This manager provides volume operations with first-class support for
    VPI leases and Hologram-specific features.
    """
    
    def __init__(self, client: Client):
        """
        Initialize volume manager.
        
        Args:
            client: Hologram client instance
        """
        self.client = client
    
    def create(
        self,
        name: str,
        driver: str = "local",
        vpi_lease: Optional[str] = None,
        **kwargs
    ) -> Dict[str, Any]:
        """
        Create a volume with Hologram features.
        
        Args:
            name: Volume name
            driver: Volume driver
            vpi_lease: Optional VPI lease for isolation
            **kwargs: Additional volume options
            
        Returns:
            Volume creation response
            
        Raises:
            VolumeError: If volume creation fails
        """
        try:
            payload = {
                "name": name,
                "driver": driver,
                "vpi_lease": vpi_lease,
                **kwargs
            }
            
            response = self.client.session.post(
                f"{self.client.base_url}/volumes/create",
                json=payload
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to create volume: {e}")
    
    def list(self, limit: Optional[int] = None, offset: Optional[int] = None) -> List[Dict[str, Any]]:
        """
        List volumes.
        
        Args:
            limit: Maximum number of volumes to return
            offset: Number of volumes to skip
            
        Returns:
            List of volume information dictionaries
            
        Raises:
            VolumeError: If listing volumes fails
        """
        try:
            params = {}
            if limit is not None:
                params["limit"] = limit
            if offset is not None:
                params["offset"] = offset
            
            response = self.client.session.get(
                f"{self.client.base_url}/volumes/list",
                params=params
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to list volumes: {e}")
    
    def get_info(self, volume_id: str) -> Dict[str, Any]:
        """
        Get volume information.
        
        Args:
            volume_id: Volume ID to get information for
            
        Returns:
            Volume information dictionary
            
        Raises:
            VolumeError: If getting volume info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/volumes/info/{volume_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to get volume info for {volume_id}: {e}")
    
    def remove(self, volume_id: str, force: bool = False) -> bool:
        """
        Remove a volume.
        
        Args:
            volume_id: Volume ID to remove
            force: Whether to force removal
            
        Returns:
            True if removal was successful
            
        Raises:
            VolumeError: If volume removal fails
        """
        try:
            params = {"force": force}
            
            response = self.client.session.delete(
                f"{self.client.base_url}/volumes/remove/{volume_id}",
                params=params
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VolumeError(f"Failed to remove volume {volume_id}: {e}")
    
    def get_hologram_info(self, volume_id: str) -> Dict[str, Any]:
        """
        Get Hologram-specific information for a volume.
        
        Args:
            volume_id: Volume ID to get Hologram info for
            
        Returns:
            Hologram information dictionary
            
        Raises:
            VolumeError: If getting Hologram info fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/volumes/hologram/{volume_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to get Hologram info for volume {volume_id}: {e}")
    
    def update_hologram_config(self, volume_id: str, config: Dict[str, Any]) -> bool:
        """
        Update Hologram configuration for a volume.
        
        Args:
            volume_id: Volume ID to update
            config: New Hologram configuration
            
        Returns:
            True if update was successful
            
        Raises:
            VolumeError: If Hologram config update fails
        """
        try:
            payload = {"config": config}
            
            response = self.client.session.put(
                f"{self.client.base_url}/volumes/hologram/{volume_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VolumeError(f"Failed to update Hologram config for volume {volume_id}: {e}")
    
    def get_metrics(self, volume_id: str) -> Dict[str, Any]:
        """
        Get volume metrics.
        
        Args:
            volume_id: Volume ID to get metrics for
            
        Returns:
            Volume metrics dictionary
            
        Raises:
            VolumeError: If getting volume metrics fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/volumes/metrics/{volume_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to get metrics for volume {volume_id}: {e}")
    
    def create_snapshot(self, volume_id: str, snapshot_config: Dict[str, Any]) -> str:
        """
        Create a snapshot of a volume.
        
        Args:
            volume_id: Volume ID to snapshot
            snapshot_config: Snapshot configuration
            
        Returns:
            Snapshot ID string
            
        Raises:
            VolumeError: If volume snapshot creation fails
        """
        try:
            payload = {"snapshot_config": snapshot_config}
            
            response = self.client.session.post(
                f"{self.client.base_url}/volumes/snapshot/{volume_id}",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["snapshot_id"]
            
        except Exception as e:
            raise VolumeError(f"Failed to create volume snapshot: {e}")
    
    def restore_snapshot(self, volume_id: str, snapshot_id: str) -> bool:
        """
        Restore a volume from a snapshot.
        
        Args:
            volume_id: Volume ID to restore
            snapshot_id: Snapshot ID to restore from
            
        Returns:
            True if restoration was successful
            
        Raises:
            VolumeError: If volume restoration fails
        """
        try:
            payload = {"snapshot_id": snapshot_id}
            
            response = self.client.session.post(
                f"{self.client.base_url}/volumes/restore/{volume_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VolumeError(f"Failed to restore volume from snapshot: {e}")
    
    def list_snapshots(self, volume_id: str) -> List[Dict[str, Any]]:
        """
        List snapshots for a volume.
        
        Args:
            volume_id: Volume ID to list snapshots for
            
        Returns:
            List of snapshot information dictionaries
            
        Raises:
            VolumeError: If listing volume snapshots fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/volumes/snapshots/{volume_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to list volume snapshots: {e}")
    
    def delete_snapshot(self, volume_id: str, snapshot_id: str) -> bool:
        """
        Delete a volume snapshot.
        
        Args:
            volume_id: Volume ID
            snapshot_id: Snapshot ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            VolumeError: If volume snapshot deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/volumes/snapshot/{volume_id}/{snapshot_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VolumeError(f"Failed to delete volume snapshot: {e}")
    
    def create_backup(self, volume_id: str, backup_config: Dict[str, Any]) -> str:
        """
        Create a backup of a volume.
        
        Args:
            volume_id: Volume ID to backup
            backup_config: Backup configuration
            
        Returns:
            Backup ID string
            
        Raises:
            VolumeError: If volume backup creation fails
        """
        try:
            payload = {"backup_config": backup_config}
            
            response = self.client.session.post(
                f"{self.client.base_url}/volumes/backup/{volume_id}",
                json=payload
            )
            response.raise_for_status()
            
            result = response.json()
            return result["backup_id"]
            
        except Exception as e:
            raise VolumeError(f"Failed to create volume backup: {e}")
    
    def restore_backup(self, volume_id: str, backup_id: str) -> bool:
        """
        Restore a volume from a backup.
        
        Args:
            volume_id: Volume ID to restore
            backup_id: Backup ID to restore from
            
        Returns:
            True if restoration was successful
            
        Raises:
            VolumeError: If volume restoration fails
        """
        try:
            payload = {"backup_id": backup_id}
            
            response = self.client.session.post(
                f"{self.client.base_url}/volumes/restore-backup/{volume_id}",
                json=payload
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VolumeError(f"Failed to restore volume from backup: {e}")
    
    def list_backups(self, volume_id: str) -> List[Dict[str, Any]]:
        """
        List backups for a volume.
        
        Args:
            volume_id: Volume ID to list backups for
            
        Returns:
            List of backup information dictionaries
            
        Raises:
            VolumeError: If listing volume backups fails
        """
        try:
            response = self.client.session.get(
                f"{self.client.base_url}/volumes/backups/{volume_id}"
            )
            response.raise_for_status()
            
            return response.json()
            
        except Exception as e:
            raise VolumeError(f"Failed to list volume backups: {e}")
    
    def delete_backup(self, volume_id: str, backup_id: str) -> bool:
        """
        Delete a volume backup.
        
        Args:
            volume_id: Volume ID
            backup_id: Backup ID to delete
            
        Returns:
            True if deletion was successful
            
        Raises:
            VolumeError: If volume backup deletion fails
        """
        try:
            response = self.client.session.delete(
                f"{self.client.base_url}/volumes/backup/{volume_id}/{backup_id}"
            )
            response.raise_for_status()
            
            return True
            
        except Exception as e:
            raise VolumeError(f"Failed to delete volume backup: {e}")

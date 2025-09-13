"""
Error classes for hologram-docker.
"""

from docker.errors import (
    DockerException as BaseDockerError,
    APIError as BaseAPIError,
    ContainerError as BaseContainerError,
    ImageNotFound as BaseImageNotFound,
    NotFound as BaseNotFound,
)


class DockerError(BaseDockerError):
    """Base exception for all Docker-related errors."""
    pass


class APIError(BaseAPIError):
    """Exception raised when Docker API returns an error."""
    pass


class ContainerError(BaseContainerError):
    """Exception raised when a container operation fails."""
    pass


class ImageNotFound(BaseImageNotFound):
    """Exception raised when an image is not found."""
    pass


class NotFound(BaseNotFound):
    """Exception raised when a resource is not found."""
    pass


class HologramError(DockerError):
    """Base exception for Hologram-specific errors."""
    pass


class UORIDError(HologramError):
    """Exception raised when UOR-ID operations fail."""
    pass


class WitnessError(HologramError):
    """Exception raised when witness operations fail."""
    pass


class VPILeaseError(HologramError):
    """Exception raised when VPI lease operations fail."""
    pass


class CTP96Error(HologramError):
    """Exception raised when CTP-96 operations fail."""
    pass

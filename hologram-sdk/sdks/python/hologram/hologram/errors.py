"""
Error classes for hologram SDK.
"""


class HologramError(Exception):
    """Base exception for all Hologram-related errors."""
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


class SpaceError(HologramError):
    """Exception raised when 12,288 space operations fail."""
    pass


class MetaError(HologramError):
    """Exception raised when meta-awareness operations fail."""
    pass


class OracleError(HologramError):
    """Exception raised when oracle operations fail."""
    pass


class ContainerError(HologramError):
    """Exception raised when container operations fail."""
    pass


class ImageError(HologramError):
    """Exception raised when image operations fail."""
    pass


class NetworkError(HologramError):
    """Exception raised when network operations fail."""
    pass


class VolumeError(HologramError):
    """Exception raised when volume operations fail."""
    pass

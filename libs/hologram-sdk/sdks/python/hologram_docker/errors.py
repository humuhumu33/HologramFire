"""
Error classes for Hologram Docker SDK.

This module provides error classes that mirror docker-py's error hierarchy.
"""


class DockerError(Exception):
    """Base exception for Docker-related errors."""
    pass


class APIError(DockerError):
    """Exception raised for API errors."""
    pass


class NotFound(DockerError):
    """Exception raised when a resource is not found."""
    pass


class ImageNotFound(NotFound):
    """Exception raised when an image is not found."""
    pass


class ContainerNotFound(NotFound):
    """Exception raised when a container is not found."""
    pass


class NetworkNotFound(NotFound):
    """Exception raised when a network is not found."""
    pass


class VolumeNotFound(NotFound):
    """Exception raised when a volume is not found."""
    pass


class BuildError(DockerError):
    """Exception raised for build errors."""
    pass


class InvalidVersion(DockerError):
    """Exception raised for invalid API version."""
    pass


class InvalidConfig(DockerError):
    """Exception raised for invalid configuration."""
    pass

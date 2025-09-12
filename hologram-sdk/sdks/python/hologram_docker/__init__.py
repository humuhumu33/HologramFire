"""
Hologram Docker-compatible client library.

This module provides a drop-in replacement for docker-py that maintains
identical API compatibility while adding optional Hologram features.
"""

from .client import DockerClient
from .api import APIClient
from .errors import DockerError, APIError, NotFound, ImageNotFound, ContainerNotFound

__version__ = "0.1.0"
__all__ = [
    "DockerClient",
    "APIClient", 
    "DockerError",
    "APIError",
    "NotFound",
    "ImageNotFound",
    "ContainerNotFound",
]

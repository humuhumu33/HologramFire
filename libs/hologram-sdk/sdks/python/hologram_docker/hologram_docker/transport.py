"""
Transport layer for hologram-docker with UNIX socket support.
"""

import os
import json
from urllib.parse import quote_plus
from typing import Optional, Dict, Any, Union

import platform

# Check if we're on Windows
IS_WINDOWS = platform.system() == "Windows"

try:
    if not IS_WINDOWS:
        import requests_unixsocket
        HAS_UNIX_SOCKET = True
    else:
        HAS_UNIX_SOCKET = False
except ImportError:
    HAS_UNIX_SOCKET = False

import requests


class APIClient:
    """
    API client with UNIX socket support for hologram-docker.
    
    This client provides the same interface as docker-py's APIClient
    but with support for UNIX sockets and Hologram features.
    """
    
    def __init__(self, base_url: Optional[str] = None, **kwargs):
        """
        Initialize API client.
        
        Args:
            base_url: Base URL for the API (default: unix:///var/run/hologramd.sock)
            **kwargs: Additional client options
        """
        if base_url is None:
            # Default to TCP on Windows, UNIX socket on Unix-like systems
            if IS_WINDOWS:
                base_url = "tcp://localhost:2375"
            else:
                base_url = "unix:///var/run/hologramd.sock"
        
        self.base_url = base_url
        self.timeout = kwargs.get('timeout', 60)
        
        # Determine transport type
        if self.base_url.startswith("unix://"):
            if IS_WINDOWS:
                raise ValueError(
                    "UNIX sockets are not supported on Windows. "
                    "Please use TCP connection (e.g., tcp://localhost:2375)"
                )
            if not HAS_UNIX_SOCKET:
                raise ImportError(
                    "requests-unixsocket is required for UNIX socket support. "
                    "Install with: pip install requests-unixsocket"
                )
            self._session = requests_unixsocket.Session()
            self._is_unix = True
            self._unix_path = self.base_url[len("unix://"):]
        else:
            self._session = requests.Session()
            self._is_unix = False
        
        # Set default headers
        self._session.headers.update({
            'User-Agent': 'hologram-docker/0.1.0',
            'Content-Type': 'application/json',
        })
    
    def _url(self, path: str) -> str:
        """
        Build full URL for a path.
        
        Args:
            path: API path
            
        Returns:
            Full URL
        """
        if self._is_unix:
            # http+unix uses percent-encoded socket path
            return f"http+unix://{quote_plus(self._unix_path)}{path}"
        return f"{self.base_url}{path}"
    
    def get(self, path: str, **kwargs) -> requests.Response:
        """
        Make GET request.
        
        Args:
            path: API path
            **kwargs: Additional request options
            
        Returns:
            Response object
        """
        url = self._url(path)
        kwargs.setdefault('timeout', self.timeout)
        return self._session.get(url, **kwargs)
    
    def post(self, path: str, **kwargs) -> requests.Response:
        """
        Make POST request.
        
        Args:
            path: API path
            **kwargs: Additional request options
            
        Returns:
            Response object
        """
        url = self._url(path)
        kwargs.setdefault('timeout', self.timeout)
        return self._session.post(url, **kwargs)
    
    def put(self, path: str, **kwargs) -> requests.Response:
        """
        Make PUT request.
        
        Args:
            path: API path
            **kwargs: Additional request options
            
        Returns:
            Response object
        """
        url = self._url(path)
        kwargs.setdefault('timeout', self.timeout)
        return self._session.put(url, **kwargs)
    
    def delete(self, path: str, **kwargs) -> requests.Response:
        """
        Make DELETE request.
        
        Args:
            path: API path
            **kwargs: Additional request options
            
        Returns:
            Response object
        """
        url = self._url(path)
        kwargs.setdefault('timeout', self.timeout)
        return self._session.delete(url, **kwargs)
    
    def ping(self) -> bool:
        """
        Ping the daemon.
        
        Returns:
            True if daemon is reachable
        """
        try:
            response = self.get("/_ping")
            return response.status_code == 200 and response.text.strip() == "OK"
        except Exception:
            return False
    
    def version(self) -> Dict[str, Any]:
        """
        Get daemon version.
        
        Returns:
            Version information
        """
        response = self.get("/version")
        response.raise_for_status()
        return response.json()
    
    def info(self) -> Dict[str, Any]:
        """
        Get daemon info.
        
        Returns:
            Daemon information
        """
        response = self.get("/info")
        response.raise_for_status()
        return response.json()
    
    def close(self) -> None:
        """Close the client and cleanup resources."""
        if hasattr(self, '_session'):
            self._session.close()
    
    def __enter__(self):
        """Context manager entry."""
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()
    
    def __del__(self):
        """Destructor."""
        self.close()

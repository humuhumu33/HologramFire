"""
API client for Hologram Docker SDK.

This module provides the low-level API client that handles HTTP communication
with the hologramd daemon.
"""

import json
import os
import socket
import urllib.parse
from typing import Any, Dict, Optional, Union, Iterator
import requests
import requests_unixsocket


class APIClient:
    """
    Low-level API client for communicating with hologramd.
    
    This class handles HTTP communication with the hologramd daemon,
    supporting both UNIX socket and TCP connections.
    """
    
    def __init__(
        self,
        base_url: str,
        version: str = '1.41',
        timeout: int = 60,
        tls: bool = False,
        user_agent: str = 'hologram-docker/0.1.0',
        use_ssh_client: bool = False,
        max_pool_size: int = 10,
        **kwargs
    ):
        """
        Initialize API client.
        
        Args:
            base_url: Base URL for the daemon
            version: API version to use
            timeout: Request timeout in seconds
            tls: Enable TLS
            user_agent: User agent string
            use_ssh_client: Use SSH client
            max_pool_size: Maximum pool size
            **kwargs: Additional arguments
        """
        self.base_url = base_url
        self.version = version
        self.timeout = timeout
        self.tls = tls
        self.user_agent = user_agent
        self.use_ssh_client = use_ssh_client
        self.max_pool_size = max_pool_size
        
        # Parse base URL
        parsed = urllib.parse.urlparse(base_url)
        self.scheme = parsed.scheme
        self.host = parsed.hostname
        self.port = parsed.port
        self.path = parsed.path
        
        # Set up session
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': user_agent,
            'Content-Type': 'application/json',
        })
        
        # Configure session based on connection type
        if self.scheme == 'unix':
            self._setup_unix_socket()
        elif self.scheme in ('tcp', 'http', 'https'):
            self._setup_tcp_connection()
        else:
            raise ValueError(f"Unsupported URL scheme: {self.scheme}")
        
        # Set up connection pooling
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=max_pool_size,
            pool_maxsize=max_pool_size
        )
        self.session.mount('http://', adapter)
        self.session.mount('https://', adapter)
    
    def _setup_unix_socket(self):
        """Set up UNIX socket connection."""
        # Use requests-unixsocket for UNIX socket support
        self.session.mount('http+unix://', requests_unixsocket.UnixAdapter())
        
        # Convert unix:///path to http+unix://path
        if self.path.startswith('/'):
            self.path = self.path[1:]
        
        self.base_url = f"http+unix://{self.path}"
    
    def _setup_tcp_connection(self):
        """Set up TCP connection."""
        if self.tls or self.scheme == 'https':
            self.base_url = f"https://{self.host}"
            if self.port:
                self.base_url += f":{self.port}"
        else:
            self.base_url = f"http://{self.host}"
            if self.port:
                self.base_url += f":{self.port}"
    
    def _build_url(self, path: str, params: Optional[Dict[str, Any]] = None) -> str:
        """
        Build full URL for API request.
        
        Args:
            path: API path
            params: Query parameters
            
        Returns:
            Full URL
        """
        # Ensure path starts with /
        if not path.startswith('/'):
            path = '/' + path
        
        # Add version prefix if not already present
        if not path.startswith(f'/v{self.version}') and not path.startswith('/_'):
            path = f'/v{self.version}{path}'
        
        url = self.base_url + path
        
        if params:
            # Convert params to query string
            query_parts = []
            for key, value in params.items():
                if isinstance(value, (list, tuple)):
                    for item in value:
                        query_parts.append(f"{key}={urllib.parse.quote(str(item))}")
                else:
                    query_parts.append(f"{key}={urllib.parse.quote(str(value))}")
            
            if query_parts:
                url += '?' + '&'.join(query_parts)
        
        return url
    
    def _make_request(
        self,
        method: str,
        path: str,
        params: Optional[Dict[str, Any]] = None,
        json_data: Optional[Dict[str, Any]] = None,
        stream: bool = False,
        **kwargs
    ) -> Union[Dict[str, Any], Iterator[Dict[str, Any]]]:
        """
        Make HTTP request to the daemon.
        
        Args:
            method: HTTP method
            path: API path
            params: Query parameters
            json_data: JSON data to send
            stream: Stream the response
            **kwargs: Additional request arguments
            
        Returns:
            Response data
        """
        url = self._build_url(path, params)
        
        # Prepare request arguments
        request_kwargs = {
            'timeout': self.timeout,
            'stream': stream,
        }
        
        if json_data is not None:
            request_kwargs['json'] = json_data
        
        # Add additional arguments
        request_kwargs.update(kwargs)
        
        try:
            response = self.session.request(method, url, **request_kwargs)
            response.raise_for_status()
            
            if stream:
                return self._stream_response(response)
            else:
                return response.json()
        
        except requests.exceptions.RequestException as e:
            raise APIError(f"Request failed: {e}")
        except json.JSONDecodeError as e:
            raise APIError(f"Failed to decode JSON response: {e}")
    
    def _stream_response(self, response: requests.Response) -> Iterator[Dict[str, Any]]:
        """
        Stream response data.
        
        Args:
            response: Response object
            
        Yields:
            Parsed JSON objects
        """
        for line in response.iter_lines(decode_unicode=True):
            if line:
                try:
                    yield json.loads(line)
                except json.JSONDecodeError:
                    # Skip invalid JSON lines
                    continue
    
    def get(self, path: str, params: Optional[Dict[str, Any]] = None, 
            stream: bool = False, **kwargs) -> Union[Dict[str, Any], Iterator[Dict[str, Any]]]:
        """Make GET request."""
        return self._make_request('GET', path, params=params, stream=stream, **kwargs)
    
    def post(self, path: str, params: Optional[Dict[str, Any]] = None,
             json_data: Optional[Dict[str, Any]] = None, stream: bool = False,
             **kwargs) -> Union[Dict[str, Any], Iterator[Dict[str, Any]]]:
        """Make POST request."""
        return self._make_request('POST', path, params=params, json_data=json_data, 
                                 stream=stream, **kwargs)
    
    def put(self, path: str, params: Optional[Dict[str, Any]] = None,
            json_data: Optional[Dict[str, Any]] = None, stream: bool = False,
            **kwargs) -> Union[Dict[str, Any], Iterator[Dict[str, Any]]]:
        """Make PUT request."""
        return self._make_request('PUT', path, params=params, json_data=json_data,
                                 stream=stream, **kwargs)
    
    def delete(self, path: str, params: Optional[Dict[str, Any]] = None,
               **kwargs) -> Union[Dict[str, Any], Iterator[Dict[str, Any]]]:
        """Make DELETE request."""
        return self._make_request('DELETE', path, params=params, **kwargs)
    
    def ping(self) -> str:
        """
        Ping the daemon.
        
        Returns:
            Ping response
        """
        response = self.get('/_ping')
        return response.text if hasattr(response, 'text') else str(response)
    
    def version(self) -> Dict[str, Any]:
        """
        Get daemon version.
        
        Returns:
            Version information
        """
        return self.get('/version')
    
    def info(self) -> Dict[str, Any]:
        """
        Get daemon system information.
        
        Returns:
            System information
        """
        return self.get('/info')
    
    def close(self):
        """Close the client and clean up resources."""
        if hasattr(self.session, 'close'):
            self.session.close()
    
    def __enter__(self):
        """Context manager entry."""
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.close()


class APIError(Exception):
    """Exception raised for API errors."""
    pass

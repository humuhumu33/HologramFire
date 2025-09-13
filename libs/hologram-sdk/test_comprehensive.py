#!/usr/bin/env python3
"""
Comprehensive test script for Hologram SDK Docker compatibility.

This script tests all the implemented features:
1. Contract checks (_ping, /version, /images/json)
2. Image pull with streaming
3. Container lifecycle MVP
4. Python client compatibility
5. Namespaced extensions
6. Error handling
"""

import json
import os
import requests
import sys
import time
from typing import Dict, Any, Optional

# Test configuration
HOLOGRAM_HOST = os.getenv('HOLOGRAM_HOST', 'http://localhost:2376')
DOCKER_HOST = os.getenv('DOCKER_HOST', 'http://localhost:2375')

class ComprehensiveTester:
    def __init__(self, hologram_host: str = HOLOGRAM_HOST, docker_host: str = DOCKER_HOST):
        self.hologram_host = hologram_host
        self.docker_host = docker_host
        self.timeout = 30
        self.passed = 0
        self.failed = 0
    
    def test(self, name: str, test_func) -> bool:
        """Run a test and track results"""
        print(f"\n{'='*60}")
        print(f"Testing: {name}")
        print(f"{'='*60}")
        
        try:
            result = test_func()
            if result:
                print(f"✓ {name} PASSED")
                self.passed += 1
            else:
                print(f"✗ {name} FAILED")
                self.failed += 1
            return result
        except Exception as e:
            print(f"✗ {name} FAILED with exception: {e}")
            self.failed += 1
            return False
    
    def test_contract_checks(self) -> bool:
        """Test 1: Contract checks (_ping, /version, /images/json)"""
        print("Testing contract checks...")
        
        # Test _ping
        try:
            resp = requests.get(f"{self.hologram_host}/_ping", timeout=self.timeout)
            if resp.status_code != 200 or resp.text.strip() != "OK":
                print(f"  ✗ _ping failed: status={resp.status_code}, body='{resp.text}'")
                return False
            print("  ✓ _ping endpoint works")
        except Exception as e:
            print(f"  ✗ _ping failed: {e}")
            return False
        
        # Test /version
        try:
            resp = requests.get(f"{self.hologram_host}/version", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ /version failed: status={resp.status_code}")
                return False
            
            version_data = resp.json()
            required_fields = ["ApiVersion", "Version", "MinAPIVersion", "Os", "Arch", "KernelVersion", "BuildTime"]
            for field in required_fields:
                if field not in version_data:
                    print(f"  ✗ /version missing field: {field}")
                    return False
            print("  ✓ /version endpoint works")
        except Exception as e:
            print(f"  ✗ /version failed: {e}")
            return False
        
        # Test /images/json
        try:
            resp = requests.get(f"{self.hologram_host}/images/json", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ /images/json failed: status={resp.status_code}")
                return False
            
            images_data = resp.json()
            if not isinstance(images_data, list):
                print(f"  ✗ /images/json returned non-list: {type(images_data)}")
                return False
            
            # Check if images have required fields
            for image in images_data:
                required_fields = ["Id", "RepoTags", "Size", "VirtualSize", "Labels", "Created"]
                for field in required_fields:
                    if field not in image:
                        print(f"  ✗ Image missing field: {field}")
                        return False
            print("  ✓ /images/json endpoint works")
        except Exception as e:
            print(f"  ✗ /images/json failed: {e}")
            return False
        
        return True
    
    def test_image_pull_streaming(self) -> bool:
        """Test 2: Image pull with streaming"""
        print("Testing image pull streaming...")
        
        try:
            resp = requests.post(
                f"{self.hologram_host}/images/create",
                params={"fromImage": "nginx", "tag": "alpine"},
                stream=True,
                timeout=self.timeout
            )
            
            if resp.status_code != 200:
                print(f"  ✗ Image pull failed: status={resp.status_code}")
                return False
            
            events = []
            for line in resp.iter_lines():
                if line:
                    try:
                        event = json.loads(line.decode('utf-8'))
                        events.append(event)
                        print(f"  → {event.get('status', 'Unknown event')}")
                    except json.JSONDecodeError:
                        continue
            
            if not events:
                print("  ✗ No events received")
                return False
            
            # Check for expected event types
            event_types = [event.get('status', '') for event in events]
            expected_events = ['Pulling from', 'Pulling fs layer', 'Downloading', 'Pull complete']
            
            found_events = 0
            for expected in expected_events:
                if any(expected in event_type for event_type in event_types):
                    found_events += 1
            
            if found_events < 2:
                print(f"  ✗ Expected events not found. Got: {event_types}")
                return False
            
            print(f"  ✓ Image pull streaming works ({len(events)} events)")
            return True
            
        except Exception as e:
            print(f"  ✗ Image pull streaming failed: {e}")
            return False
    
    def test_container_lifecycle(self) -> bool:
        """Test 3: Container lifecycle MVP"""
        print("Testing container lifecycle...")
        
        try:
            # Test container list
            resp = requests.get(f"{self.hologram_host}/containers/json", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ Container list failed: status={resp.status_code}")
                return False
            print("  ✓ Container list works")
            
            # Test container create
            create_data = {
                "Image": "hello-world:latest",
                "Cmd": ["/hello"],
                "Labels": {"test": "hologram"}
            }
            resp = requests.post(
                f"{self.hologram_host}/containers/create",
                json=create_data,
                timeout=self.timeout
            )
            if resp.status_code != 201:
                print(f"  ✗ Container create failed: status={resp.status_code}")
                return False
            
            create_result = resp.json()
            container_id = create_result.get('Id')
            if not container_id:
                print("  ✗ Container create missing ID")
                return False
            print(f"  ✓ Container create works (ID: {container_id[:12]})")
            
            # Test container inspect
            resp = requests.get(f"{self.hologram_host}/containers/{container_id}/json", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ Container inspect failed: status={resp.status_code}")
                return False
            print("  ✓ Container inspect works")
            
            # Test container start
            resp = requests.post(f"{self.hologram_host}/containers/{container_id}/start", timeout=self.timeout)
            if resp.status_code != 204:
                print(f"  ✗ Container start failed: status={resp.status_code}")
                return False
            print("  ✓ Container start works")
            
            # Test container logs
            resp = requests.get(f"{self.hologram_host}/containers/{container_id}/logs", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ Container logs failed: status={resp.status_code}")
                return False
            print("  ✓ Container logs work")
            
            # Test container stop
            resp = requests.post(f"{self.hologram_host}/containers/{container_id}/stop", timeout=self.timeout)
            if resp.status_code != 204:
                print(f"  ✗ Container stop failed: status={resp.status_code}")
                return False
            print("  ✓ Container stop works")
            
            # Test container delete
            resp = requests.delete(f"{self.hologram_host}/containers/{container_id}", timeout=self.timeout)
            if resp.status_code != 204:
                print(f"  ✗ Container delete failed: status={resp.status_code}")
                return False
            print("  ✓ Container delete works")
            
            return True
            
        except Exception as e:
            print(f"  ✗ Container lifecycle failed: {e}")
            return False
    
    def test_namespaced_extensions(self) -> bool:
        """Test 4: Namespaced extensions (verbose mode)"""
        print("Testing namespaced extensions...")
        
        try:
            # Test without verbose mode
            resp = requests.get(f"{self.hologram_host}/images/json", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ Images list failed: status={resp.status_code}")
                return False
            
            images = resp.json()
            has_xhologram = False
            for image in images:
                if 'XHologram' in str(image):
                    has_xhologram = True
                    break
            
            if has_xhologram:
                print("  ✗ XHologram data found in non-verbose mode")
                return False
            print("  ✓ Non-verbose mode excludes XHologram data")
            
            # Test with verbose mode
            resp = requests.get(f"{self.hologram_host}/images/json?verbose=true", timeout=self.timeout)
            if resp.status_code != 200:
                print(f"  ✗ Images list with verbose failed: status={resp.status_code}")
                return False
            
            images = resp.json()
            has_xhologram = False
            for image in images:
                if 'XHologram' in str(image):
                    has_xhologram = True
                    break
            
            if not has_xhologram:
                print("  ✗ XHologram data not found in verbose mode")
                return False
            print("  ✓ Verbose mode includes XHologram data")
            
            return True
            
        except Exception as e:
            print(f"  ✗ Namespaced extensions failed: {e}")
            return False
    
    def test_error_handling(self) -> bool:
        """Test 5: Error handling"""
        print("Testing error handling...")
        
        try:
            # Test invalid image pull
            resp = requests.post(
                f"{self.hologram_host}/images/create",
                params={"fromImage": ""},  # Invalid empty image
                timeout=self.timeout
            )
            if resp.status_code != 400:
                print(f"  ✗ Invalid image pull should return 400, got {resp.status_code}")
                return False
            
            error_data = resp.json()
            if 'message' not in error_data:
                print("  ✗ Error response missing message field")
                return False
            print("  ✓ Error handling works for invalid requests")
            
            # Test container not found
            resp = requests.get(f"{self.hologram_host}/containers/nonexistent/json", timeout=self.timeout)
            if resp.status_code != 404:
                print(f"  ✗ Container not found should return 404, got {resp.status_code}")
                return False
            print("  ✓ Error handling works for not found resources")
            
            return True
            
        except Exception as e:
            print(f"  ✗ Error handling failed: {e}")
            return False
    
    def test_python_client_compatibility(self) -> bool:
        """Test 6: Python client compatibility"""
        print("Testing Python client compatibility...")
        
        try:
            # Test basic client creation
            from hologram_docker import DockerClient
            
            client = DockerClient(base_url=self.hologram_host)
            print("  ✓ Client creation works")
            
            # Test ping
            if not client.ping():
                print("  ✗ Client ping failed")
                return False
            print("  ✓ Client ping works")
            
            # Test version
            version = client.version()
            if not isinstance(version, dict) or 'ApiVersion' not in version:
                print("  ✗ Client version failed")
                return False
            print("  ✓ Client version works")
            
            # Test images list
            images = client.images.list()
            if not isinstance(images, list):
                print("  ✗ Client images list failed")
                return False
            print("  ✓ Client images list works")
            
            # Test streaming pull
            events = list(client.images.pull("nginx", tag="alpine", stream=True))
            if not events:
                print("  ✗ Client streaming pull failed")
                return False
            print(f"  ✓ Client streaming pull works ({len(events)} events)")
            
            return True
            
        except Exception as e:
            print(f"  ✗ Python client compatibility failed: {e}")
            return False
    
    def run_all_tests(self) -> bool:
        """Run all comprehensive tests"""
        print("Hologram SDK Comprehensive Test Suite")
        print("=" * 60)
        
        tests = [
            ("Contract Checks", self.test_contract_checks),
            ("Image Pull Streaming", self.test_image_pull_streaming),
            ("Container Lifecycle", self.test_container_lifecycle),
            ("Namespaced Extensions", self.test_namespaced_extensions),
            ("Error Handling", self.test_error_handling),
            ("Python Client Compatibility", self.test_python_client_compatibility),
        ]
        
        for name, test_func in tests:
            self.test(name, test_func)
        
        print(f"\n{'='*60}")
        print(f"Test Results: {self.passed} passed, {self.failed} failed")
        print(f"{'='*60}")
        
        if self.failed == 0:
            print("🎉 All tests passed! Hologram SDK is working correctly.")
            return True
        else:
            print("❌ Some tests failed. Please check the output above.")
            return False

def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Comprehensive Hologram SDK test suite")
    parser.add_argument("--hologram-host", default=HOLOGRAM_HOST, 
                       help="Hologram daemon host")
    parser.add_argument("--docker-host", default=DOCKER_HOST, 
                       help="Docker daemon host (for comparison)")
    
    args = parser.parse_args()
    
    tester = ComprehensiveTester(args.hologram_host, args.docker_host)
    success = tester.run_all_tests()
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()

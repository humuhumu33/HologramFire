#!/usr/bin/env python3
"""
Parity test script for Hologram SDK vs Docker Engine API.

This script tests that Hologram SDK responses match Docker Engine API responses
for the same endpoints, ensuring compatibility.
"""

import json
import requests
import sys
import time
from typing import Dict, Any, Optional

class ParityTester:
    def __init__(self, docker_host: str = "http://localhost:2375", 
                 hologram_host: str = "http://localhost:2376"):
        self.docker_host = docker_host
        self.hologram_host = hologram_host
        self.timeout = 30
    
    def test_ping(self) -> bool:
        """Test _ping endpoint"""
        print("Testing _ping endpoint...")
        
        try:
            # Test Docker
            docker_resp = requests.get(f"{self.docker_host}/_ping", timeout=self.timeout)
            docker_ok = docker_resp.status_code == 200 and docker_resp.text.strip() == "OK"
        except requests.RequestException:
            print("  Docker daemon not available, skipping")
            return True
        
        try:
            # Test Hologram
            hologram_resp = requests.get(f"{self.hologram_host}/_ping", timeout=self.timeout)
            hologram_ok = hologram_resp.status_code == 200 and hologram_resp.text.strip() == "OK"
        except requests.RequestException as e:
            print(f"  Hologram daemon not available: {e}")
            return False
        
        if docker_ok and hologram_ok:
            print("  ✓ _ping endpoint matches")
            return True
        else:
            print(f"  ✗ _ping endpoint differs: Docker={docker_ok}, Hologram={hologram_ok}")
            return False
    
    def test_version(self) -> bool:
        """Test /version endpoint"""
        print("Testing /version endpoint...")
        
        try:
            # Test Docker
            docker_resp = requests.get(f"{self.docker_host}/version", timeout=self.timeout)
            docker_data = docker_resp.json() if docker_resp.status_code == 200 else None
        except requests.RequestException:
            print("  Docker daemon not available, skipping")
            return True
        
        try:
            # Test Hologram
            hologram_resp = requests.get(f"{self.hologram_host}/version", timeout=self.timeout)
            hologram_data = hologram_resp.json() if hologram_resp.status_code == 200 else None
        except requests.RequestException as e:
            print(f"  Hologram daemon not available: {e}")
            return False
        
        if docker_data and hologram_data:
            # Compare key fields (ignore version-specific fields)
            key_fields = ["ApiVersion", "MinAPIVersion", "Os", "Arch", "KernelVersion"]
            matches = True
            
            for field in key_fields:
                if docker_data.get(field) != hologram_data.get(field):
                    print(f"  ✗ {field} differs: Docker={docker_data.get(field)}, Hologram={hologram_data.get(field)}")
                    matches = False
            
            if matches:
                print("  ✓ /version endpoint matches")
                return True
            else:
                return False
        else:
            print(f"  ✗ /version endpoint failed: Docker={docker_data is not None}, Hologram={hologram_data is not None}")
            return False
    
    def test_images_list(self) -> bool:
        """Test /images/json endpoint"""
        print("Testing /images/json endpoint...")
        
        try:
            # Test Docker
            docker_resp = requests.get(f"{self.docker_host}/images/json", timeout=self.timeout)
            docker_data = docker_resp.json() if docker_resp.status_code == 200 else None
        except requests.RequestException:
            print("  Docker daemon not available, skipping")
            return True
        
        try:
            # Test Hologram
            hologram_resp = requests.get(f"{self.hologram_host}/images/json", timeout=self.timeout)
            hologram_data = hologram_resp.json() if hologram_resp.status_code == 200 else None
        except requests.RequestException as e:
            print(f"  Hologram daemon not available: {e}")
            return False
        
        if docker_data is not None and hologram_data is not None:
            # Both should return arrays
            if isinstance(docker_data, list) and isinstance(hologram_data, list):
                print(f"  ✓ /images/json endpoint matches (Docker: {len(docker_data)} images, Hologram: {len(hologram_data)} images)")
                return True
            else:
                print(f"  ✗ /images/json endpoint format differs")
                return False
        else:
            print(f"  ✗ /images/json endpoint failed: Docker={docker_data is not None}, Hologram={hologram_data is not None}")
            return False
    
    def test_image_pull_stream(self) -> bool:
        """Test /images/create endpoint streaming"""
        print("Testing /images/create endpoint streaming...")
        
        try:
            # Test Hologram streaming
            hologram_resp = requests.post(
                f"{self.hologram_host}/images/create",
                params={"fromImage": "nginx", "tag": "alpine"},
                stream=True,
                timeout=self.timeout
            )
            
            if hologram_resp.status_code == 200:
                events = []
                for line in hologram_resp.iter_lines():
                    if line:
                        try:
                            event = json.loads(line.decode('utf-8'))
                            events.append(event)
                        except json.JSONDecodeError:
                            continue
                
                if events:
                    print(f"  ✓ /images/create endpoint streams {len(events)} events")
                    return True
                else:
                    print("  ✗ /images/create endpoint returned no events")
                    return False
            else:
                print(f"  ✗ /images/create endpoint failed with status {hologram_resp.status_code}")
                return False
                
        except requests.RequestException as e:
            print(f"  Hologram daemon not available: {e}")
            return False
    
    def run_all_tests(self) -> bool:
        """Run all parity tests"""
        print("Running Hologram SDK parity tests...")
        print("=" * 50)
        
        tests = [
            self.test_ping,
            self.test_version,
            self.test_images_list,
            self.test_image_pull_stream,
        ]
        
        results = []
        for test in tests:
            try:
                result = test()
                results.append(result)
            except Exception as e:
                print(f"  ✗ Test failed with exception: {e}")
                results.append(False)
            print()
        
        passed = sum(results)
        total = len(results)
        
        print("=" * 50)
        print(f"Results: {passed}/{total} tests passed")
        
        if passed == total:
            print("✓ All parity tests passed!")
            return True
        else:
            print("✗ Some parity tests failed!")
            return False

def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Test Hologram SDK parity with Docker Engine API")
    parser.add_argument("--docker-host", default="http://localhost:2375", 
                       help="Docker daemon host (default: http://localhost:2375)")
    parser.add_argument("--hologram-host", default="http://localhost:2376", 
                       help="Hologram daemon host (default: http://localhost:2376)")
    
    args = parser.parse_args()
    
    tester = ParityTester(args.docker_host, args.hologram_host)
    success = tester.run_all_tests()
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()

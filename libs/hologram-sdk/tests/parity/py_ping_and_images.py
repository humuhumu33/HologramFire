#!/usr/bin/env python3
"""
Parity test for hologram-docker: ping and images functionality.

This test verifies that hologram-docker provides the same UX as docker-py
for basic operations like ping and listing images.
"""

import sys
import os

# Add the SDK to the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../sdks/python/hologram_docker'))

try:
    import hologram_docker as docker
except ImportError as e:
    print(f"Failed to import hologram_docker: {e}")
    print("Make sure to install dependencies: pip install -e ../../sdks/python/hologram_docker")
    sys.exit(1)


def test_ping():
    """Test ping functionality."""
    print("Testing ping...")
    
    try:
        client = docker.from_env()
        ping_result = client.api.get("/_ping")
        
        print(f"Ping status: {ping_result.status_code}")
        print(f"Ping response: {ping_result.text}")
        
        if ping_result.status_code == 200 and ping_result.text.strip() == "OK":
            print("✅ Ping test passed")
            return True
        else:
            print("❌ Ping test failed")
            return False
            
    except Exception as e:
        print(f"❌ Ping test failed with error: {e}")
        return False


def test_version():
    """Test version functionality."""
    print("\nTesting version...")
    
    try:
        client = docker.from_env()
        version_info = client.api.version()
        
        print(f"Version info: {version_info}")
        
        # Check for required fields
        required_fields = ["Version", "ApiVersion", "GoVersion", "Os", "Arch"]
        for field in required_fields:
            if field not in version_info:
                print(f"❌ Version test failed: missing field '{field}'")
                return False
        
        print("✅ Version test passed")
        return True
        
    except Exception as e:
        print(f"❌ Version test failed with error: {e}")
        return False


def test_images_list():
    """Test images list functionality."""
    print("\nTesting images list...")
    
    try:
        client = docker.from_env()
        images = client.images.list()
        
        print(f"Images count: {len(images)}")
        print(f"Images: {images}")
        
        # Check that we got a list
        if not isinstance(images, list):
            print("❌ Images list test failed: expected list, got {type(images)}")
            return False
        
        # If we have images, check the structure
        if images:
            image = images[0]
            required_fields = ["Id", "RepoTags", "Created", "Size", "VirtualSize"]
            for field in required_fields:
                if field not in image:
                    print(f"❌ Images list test failed: missing field '{field}' in image")
                    return False
        
        print("✅ Images list test passed")
        return True
        
    except Exception as e:
        print(f"❌ Images list test failed with error: {e}")
        return False


def test_docker_py_compatibility():
    """Test that the client has the same interface as docker-py."""
    print("\nTesting docker-py compatibility...")
    
    try:
        client = docker.from_env()
        
        # Check that we have the expected attributes
        expected_attrs = ["api", "images", "containers", "networks", "volumes"]
        for attr in expected_attrs:
            if not hasattr(client, attr):
                print(f"❌ Compatibility test failed: missing attribute '{attr}'")
                return False
        
        # Check that images has the expected methods
        expected_methods = ["list", "get", "pull", "push", "remove", "tag"]
        for method in expected_methods:
            if not hasattr(client.images, method):
                print(f"❌ Compatibility test failed: missing method 'images.{method}'")
                return False
        
        print("✅ Docker-py compatibility test passed")
        return True
        
    except Exception as e:
        print(f"❌ Compatibility test failed with error: {e}")
        return False


def main():
    """Run all tests."""
    print("Hologram Docker Parity Test")
    print("=" * 40)
    
    tests = [
        test_ping,
        test_version,
        test_images_list,
        test_docker_py_compatibility,
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        if test():
            passed += 1
    
    print("\n" + "=" * 40)
    print(f"Results: {passed}/{total} tests passed")
    
    if passed == total:
        print("🎉 All tests passed! Hologram Docker is working correctly.")
        return 0
    else:
        print("❌ Some tests failed. Check the output above.")
        return 1


if __name__ == "__main__":
    sys.exit(main())

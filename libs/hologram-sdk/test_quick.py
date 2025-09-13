#!/usr/bin/env python3
"""
Quick test for hologram-docker functionality.
"""

import sys
import os

# Add the SDK to the path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'sdks/python/hologram_docker'))

try:
    import hologram_docker as docker
    print("✅ Successfully imported hologram_docker")
except ImportError as e:
    print(f"❌ Failed to import hologram_docker: {e}")
    sys.exit(1)

def test_basic_functionality():
    """Test basic functionality."""
    print("\nTesting basic functionality...")
    
    try:
        # Create client (will use TCP for Windows)
        client = docker.from_env()
        print("✅ Created client successfully")
        
        # Test ping
        ping_result = client.api.get("/_ping")
        print(f"✅ Ping: {ping_result.status_code} - {ping_result.text}")
        
        # Test version
        version_info = client.api.version()
        print(f"✅ Version: {version_info.get('Version', 'unknown')}")
        
        # Test images list
        images = client.images.list()
        print(f"✅ Images: Found {len(images)} images")
        
        if images:
            print(f"   First image: {images[0].get('RepoTags', ['untagged'])[0]}")
        
        return True
        
    except Exception as e:
        print(f"❌ Test failed: {e}")
        return False

if __name__ == "__main__":
    print("Hologram Docker Quick Test")
    print("=" * 30)
    
    if test_basic_functionality():
        print("\n🎉 All tests passed!")
        sys.exit(0)
    else:
        print("\n❌ Tests failed!")
        sys.exit(1)

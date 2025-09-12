#!/usr/bin/env python3
"""
Test: Run docker run hello-world against Hologram
This script demonstrates running hello-world container through Hologram SDK
"""

import sys
import os
import time

def test_hello_world_hologram():
    """Test running hello-world container through Hologram SDK"""
    print("🚀 Testing: docker run hello-world against Hologram")
    print("=" * 60)
    
    try:
        import hologram_docker as docker
        print("✅ Successfully imported hologram_docker")
        
        # Create client
        try:
            client = docker.from_env()
            print("✅ Successfully created Hologram Docker client")
        except Exception as e:
            print(f"⚠️  Client creation failed (daemon not running): {e}")
            print("   This is expected - hologramd daemon needs to be running")
            return False
        
        # Test basic connectivity
        try:
            version_info = client.version()
            print(f"✅ Connected to daemon: {version_info.get('Version', 'unknown')}")
        except Exception as e:
            print(f"❌ Failed to get version: {e}")
            return False
        
        # List images to see what's available
        try:
            images = client.images.list()
            print(f"✅ Found {len(images)} images")
            for img in images:
                print(f"   - {img.tags[0] if img.tags else img.short_id}")
        except Exception as e:
            print(f"❌ Failed to list images: {e}")
            return False
        
        # Try to run hello-world container
        try:
            print("\n🐳 Running hello-world container...")
            container = client.containers.run(
                "hello-world:latest",
                remove=True,
                detach=False
            )
            print("✅ Hello-world container executed successfully!")
            print(f"   Output: {container.decode('utf-8') if isinstance(container, bytes) else container}")
            return True
            
        except Exception as e:
            print(f"❌ Failed to run hello-world container: {e}")
            print("   This might be because:")
            print("   1. hello-world image is not available")
            print("   2. hologramd daemon is not running")
            print("   3. Container runtime issues")
            return False
            
    except ImportError as e:
        print(f"❌ Failed to import hologram_docker: {e}")
        return False

def test_regular_docker_comparison():
    """Test with regular Docker for comparison"""
    print("\n🔄 Comparison: Testing with regular Docker")
    print("-" * 40)
    
    try:
        import docker as regular_docker
        print("✅ Successfully imported regular docker")
        
        # Reset DOCKER_HOST to use regular Docker
        old_host = os.environ.get('DOCKER_HOST')
        if 'DOCKER_HOST' in os.environ:
            del os.environ['DOCKER_HOST']
        
        try:
            client = regular_docker.from_env()
            print("✅ Successfully created regular Docker client")
            
            # Run hello-world with regular Docker
            print("🐳 Running hello-world with regular Docker...")
            container = client.containers.run(
                "hello-world:latest",
                remove=True,
                detach=False
            )
            print("✅ Regular Docker hello-world executed successfully!")
            print(f"   Output: {container.decode('utf-8') if isinstance(container, bytes) else container}")
            
        finally:
            # Restore DOCKER_HOST
            if old_host:
                os.environ['DOCKER_HOST'] = old_host
        
        return True
        
    except ImportError:
        print("⚠️  Regular docker module not available for comparison")
        return False
    except Exception as e:
        print(f"❌ Regular Docker test failed: {e}")
        return False

def main():
    """Run the hello-world test against Hologram"""
    print("🧪 Hologram Hello-World Test")
    print("=" * 60)
    
    # Test with Hologram
    hologram_success = test_hello_world_hologram()
    
    # Test with regular Docker for comparison
    docker_success = test_regular_docker_comparison()
    
    print("\n" + "=" * 60)
    print("📊 Test Results:")
    print(f"   Hologram SDK: {'✅ PASSED' if hologram_success else '❌ FAILED'}")
    print(f"   Regular Docker: {'✅ PASSED' if docker_success else '❌ FAILED'}")
    
    if hologram_success:
        print("\n🎉 SUCCESS: Hello-world container ran successfully through Hologram!")
        print("   This demonstrates Docker compatibility with Hologram SDK")
    elif docker_success:
        print("\n⚠️  PARTIAL SUCCESS: Regular Docker works, but Hologram daemon needs to be running")
        print("   To run against Hologram:")
        print("   1. Start hologramd daemon")
        print("   2. Set DOCKER_HOST to point to hologramd")
        print("   3. Re-run this test")
    else:
        print("\n❌ FAILED: Both Hologram and regular Docker tests failed")
        print("   Check Docker installation and daemon status")
    
    return hologram_success

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)

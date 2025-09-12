#!/usr/bin/env python3
"""
Test script for hologramd daemon.

This script tests the basic functionality of the hologramd daemon
to ensure Docker API compatibility and Hologram extensions work correctly.
"""

import json
import requests
import requests_unixsocket
import time
import sys
import os


def test_ping():
    """Test ping endpoint."""
    print("Testing ping endpoint...")
    try:
        response = requests.get('http+unix://%2Fvar%2Frun%2Fhologramd.sock/_ping')
        if response.status_code == 200 and response.text.strip() == "OK":
            print("✓ Ping successful")
            return True
        else:
            print(f"✗ Ping failed: {response.status_code} - {response.text}")
            return False
    except Exception as e:
        print(f"✗ Ping failed: {e}")
        return False


def test_version():
    """Test version endpoint."""
    print("Testing version endpoint...")
    try:
        response = requests.get('http+unix://%2Fvar%2Frun%2Fhologramd.sock/version')
        if response.status_code == 200:
            version_data = response.json()
            if 'ApiVersion' in version_data and 'Version' in version_data:
                print(f"✓ Version successful: {version_data['Version']} (API {version_data['ApiVersion']})")
                return True
            else:
                print(f"✗ Version response missing required fields: {version_data}")
                return False
        else:
            print(f"✗ Version failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"✗ Version failed: {e}")
        return False


def test_info():
    """Test info endpoint."""
    print("Testing info endpoint...")
    try:
        response = requests.get('http+unix://%2Fvar%2Frun%2Fhologramd.sock/info')
        if response.status_code == 200:
            info_data = response.json()
            if 'ID' in info_data and 'Containers' in info_data:
                print(f"✓ Info successful: {info_data['ID']}")
                return True
            else:
                print(f"✗ Info response missing required fields: {info_data}")
                return False
        else:
            print(f"✗ Info failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"✗ Info failed: {e}")
        return False


def test_images_list():
    """Test images list endpoint."""
    print("Testing images list endpoint...")
    try:
        response = requests.get('http+unix://%2Fvar%2Frun%2Fhologramd.sock/images/json')
        if response.status_code == 200:
            images = response.json()
            if isinstance(images, list):
                print(f"✓ Images list successful: {len(images)} images")
                return True
            else:
                print(f"✗ Images list response not a list: {images}")
                return False
        else:
            print(f"✗ Images list failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"✗ Images list failed: {e}")
        return False


def test_images_list_verbose():
    """Test images list endpoint with verbose mode."""
    print("Testing images list endpoint with verbose mode...")
    try:
        response = requests.get('http+unix://%2Fvar%2Frun%2Fhologramd.sock/images/json?verbose=true')
        if response.status_code == 200:
            images = response.json()
            if isinstance(images, list):
                # Check if any image has XHologram extensions
                has_hologram = any('XHologram' in str(image) for image in images)
                print(f"✓ Images list verbose successful: {len(images)} images, Hologram extensions: {has_hologram}")
                return True
            else:
                print(f"✗ Images list verbose response not a list: {images}")
                return False
        else:
            print(f"✗ Images list verbose failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"✗ Images list verbose failed: {e}")
        return False


def test_images_create():
    """Test images create endpoint."""
    print("Testing images create endpoint...")
    try:
        response = requests.post('http+unix://%2Fvar%2Frun%2Fhologramd.sock/images/create?fromImage=nginx&tag=alpine')
        if response.status_code == 200:
            # Check if response is streaming JSON
            lines = response.text.strip().split('\n')
            if lines and lines[0].startswith('{'):
                print(f"✓ Images create successful: {len(lines)} progress lines")
                return True
            else:
                print(f"✗ Images create response not JSON: {response.text[:100]}")
                return False
        else:
            print(f"✗ Images create failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"✗ Images create failed: {e}")
        return False


def test_images_create_verbose():
    """Test images create endpoint with verbose mode."""
    print("Testing images create endpoint with verbose mode...")
    try:
        response = requests.post('http+unix://%2Fvar%2Frun%2Fhologramd.sock/images/create?fromImage=nginx&tag=alpine&verbose=true')
        if response.status_code == 200:
            # Check if response is streaming JSON
            lines = response.text.strip().split('\n')
            if lines and lines[0].startswith('{'):
                # Check if any line contains Hologram-specific content
                has_hologram = any('UOR-ID' in line or 'witness' in line for line in lines)
                print(f"✓ Images create verbose successful: {len(lines)} progress lines, Hologram content: {has_hologram}")
                return True
            else:
                print(f"✗ Images create verbose response not JSON: {response.text[:100]}")
                return False
        else:
            print(f"✗ Images create verbose failed: {response.status_code}")
            return False
    except Exception as e:
        print(f"✗ Images create verbose failed: {e}")
        return False


def main():
    """Run all tests."""
    print("Hologramd Test Suite")
    print("==================")
    
    # Check if daemon is running
    if not os.path.exists('/var/run/hologramd.sock'):
        print("✗ Hologramd daemon not running (socket not found)")
        print("Please start hologramd first:")
        print("  cd hologram-sdk/engine && go run cmd/hologramd/main.go")
        sys.exit(1)
    
    # Register requests-unixsocket
    requests_unixsocket.monkeypatch()
    
    tests = [
        test_ping,
        test_version,
        test_info,
        test_images_list,
        test_images_list_verbose,
        test_images_create,
        test_images_create_verbose,
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            print(f"✗ Test {test.__name__} failed with exception: {e}")
        print()
    
    print("Test Results")
    print("============")
    print(f"Passed: {passed}/{total}")
    
    if passed == total:
        print("✓ All tests passed!")
        sys.exit(0)
    else:
        print("✗ Some tests failed!")
        sys.exit(1)


if __name__ == '__main__':
    main()

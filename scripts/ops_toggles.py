#!/usr/bin/env python3
"""
Quick ops toggles for Hologram pipeline configuration.
Provides easy copy/paste configurations for different environments.
"""
import os
from typing import Dict, Any

# Environment configurations
CONFIGS = {
    "pr": {
        "description": "Pull Request - Fast tests, lenient budgets",
        "env_vars": {
            "SLO_VERIFY_P95_MS": "15",
            "SLO_ENCODE_P95_MS": "150", 
            "SLO_GQL_P95_MS": "150",
            "GQL_SAMPLES": "20",
            "GQL_WARMUP": "3",
            "ENC_MB": "1"
        }
    },
    "main": {
        "description": "Main branch - Full tests, strict budgets",
        "env_vars": {
            "SLO_VERIFY_P95_MS": "8",
            "SLO_ENCODE_P95_MS": "80",
            "SLO_GQL_P95_MS": "80", 
            "GQL_SAMPLES": "100",
            "GQL_WARMUP": "10",
            "ENC_MB": "4"
        }
    },
    "nightly": {
        "description": "Nightly - Full tests, standard budgets",
        "env_vars": {
            "SLO_VERIFY_P95_MS": "10",
            "SLO_ENCODE_P95_MS": "100",
            "SLO_GQL_P95_MS": "100",
            "GQL_SAMPLES": "100", 
            "GQL_WARMUP": "10",
            "ENC_MB": "4"
        }
    },
    "dev": {
        "description": "Local development - Relaxed for debugging",
        "env_vars": {
            "SLO_VERIFY_P95_MS": "50",
            "SLO_ENCODE_P95_MS": "500",
            "SLO_GQL_P95_MS": "500",
            "GQL_SAMPLES": "5",
            "GQL_WARMUP": "1", 
            "ENC_MB": "1"
        }
    }
}

# Common endpoints
ENDPOINTS = {
    "local": {
        "IPFS_API": "http://127.0.0.1:5001",
        "GRAPHQL_URL": "http://localhost:4000/graphql"
    },
    "staging": {
        "IPFS_API": "https://ipfs-staging.example.com",
        "GRAPHQL_URL": "https://graphql-staging.example.com/graphql"
    },
    "production": {
        "IPFS_API": "https://ipfs.example.com", 
        "GRAPHQL_URL": "https://graphql.example.com/graphql"
    }
}

def print_config(config_name: str, endpoint_name: str = "local"):
    """Print configuration for copy/paste."""
    if config_name not in CONFIGS:
        print(f"❌ Unknown config: {config_name}")
        print(f"Available: {', '.join(CONFIGS.keys())}")
        return
    
    if endpoint_name not in ENDPOINTS:
        print(f"❌ Unknown endpoint: {endpoint_name}")
        print(f"Available: {', '.join(ENDPOINTS.keys())}")
        return
    
    config = CONFIGS[config_name]
    endpoints = ENDPOINTS[endpoint_name]
    
    print(f"🔥 {config['description']}")
    print(f"📍 Endpoints: {endpoint_name}")
    print()
    
    # Performance budgets
    print("# Performance Budgets")
    budget_vars = {k: v for k, v in config["env_vars"].items() if k.startswith("SLO_")}
    for key, value in budget_vars.items():
        print(f"export {key}={value}")
    print()
    
    # Sample sizes
    print("# Sample Sizes")
    sample_vars = {k: v for k, v in config["env_vars"].items() if not k.startswith("SLO_")}
    for key, value in sample_vars.items():
        print(f"export {key}={value}")
    print()
    
    # Endpoints
    print("# Endpoints")
    for key, value in endpoints.items():
        print(f"export {key}={value}")
    print()
    
    # Windows PowerShell
    print("# Windows PowerShell")
    for key, value in config["env_vars"].items():
        print(f"$env:{key}=\"{value}\"")
    for key, value in endpoints.items():
        print(f"$env:{key}=\"{value}\"")
    print()

def print_all_configs():
    """Print all configurations."""
    print("🔥 Hologram Pipeline - Quick Ops Toggles")
    print("=" * 50)
    print()
    
    for config_name in CONFIGS:
        print_config(config_name, "local")
        print("-" * 30)
        print()

def main():
    """Main function."""
    import sys
    
    if len(sys.argv) == 1:
        print_all_configs()
    elif len(sys.argv) == 2:
        config_name = sys.argv[1]
        print_config(config_name, "local")
    elif len(sys.argv) == 3:
        config_name = sys.argv[1]
        endpoint_name = sys.argv[2]
        print_config(config_name, endpoint_name)
    else:
        print("Usage: python scripts/ops_toggles.py [config] [endpoint]")
        print(f"Configs: {', '.join(CONFIGS.keys())}")
        print(f"Endpoints: {', '.join(ENDPOINTS.keys())}")

if __name__ == "__main__":
    main()

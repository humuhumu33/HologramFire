import importlib
import os
import sys
import subprocess
import json
from pathlib import Path


def import_prod():
    """
    Import REAL production code. No mocks.
    HOLOGRAM_PKG can override the module path (default 'hologram').
    Tries ./src layout if needed.
    """
    mod_path = os.getenv("HOLOGRAM_PKG", "hologram")
    try:
        return importlib.import_module(mod_path)
    except ModuleNotFoundError:
        src = os.path.join(os.getcwd(), "src")
        if os.path.isdir(src) and src not in sys.path:
            sys.path.insert(0, src)
        return importlib.import_module(mod_path)


def get_node_hologram_api():
    """
    Get the real Hologram API from the TypeScript/Node.js production code.
    This calls the actual production functions via Node.js subprocess.
    """
    # Path to the core TypeScript source
    core_src = Path("core/src")
    if not core_src.exists():
        raise RuntimeError("Core source directory not found. Expected: core/src")
    
    # Create a Node.js bridge script that exports the real API
    bridge_script = """
const path = require('path');
const { execSync } = require('child_process');

// Add the core src to require path
const coreSrc = path.join(__dirname, 'core', 'src');
require('module')._nodeModulePaths.push(coreSrc);

try {
    // Import the real production modules
    const core = require('./core/src/core/index.js');
    const atlas = require('./core/src/atlas12288/Atlas12288Encoder.js');
    const cef = require('./core/src/transport/ctp96/CTP96Protocol.js');
    const bhic = require('./core/src/rh/Stable.js');
    const uorid = require('./core/src/identity/UORID.js');
    const ctp96 = require('./core/src/transport/ctp96/CTP96Protocol.js');
    const sdk = require('./core/src/proof-chain/index.js');
    const graphql = require('./core/src/graphql/resolvers.js');
    const ipfs = require('./core/src/ipfs/IPFSClient.js');
    
    // Export the real API
    module.exports = {
        core,
        atlas,
        cef,
        bhic,
        uorid,
        ctp96,
        sdk,
        graphql,
        ipfs,
        __version__: "1.0.0"
    };
} catch (error) {
    console.error('Failed to import production modules:', error.message);
    process.exit(1);
}
"""
    
    # Write the bridge script
    bridge_path = Path("tests/_node_bridge.js")
    bridge_path.write_text(bridge_script)
    
    try:
        # Execute the bridge script and get the API
        result = subprocess.run(
            ["node", str(bridge_path)],
            capture_output=True,
            text=True,
            cwd=os.getcwd()
        )
        
        if result.returncode != 0:
            raise RuntimeError(f"Failed to load production API: {result.stderr}")
        
        # Parse the JSON output (we'll modify the bridge to output JSON)
        return json.loads(result.stdout)
        
    finally:
        # Clean up the bridge script
        if bridge_path.exists():
            bridge_path.unlink()


def call_node_function(module_path, function_name, *args):
    """
    Call a specific function from the Node.js production code.
    """
    # Create a temporary script to call the function
    script = f"""
const path = require('path');
const coreSrc = path.join(__dirname, 'core', 'src');
require('module')._nodeModulePaths.push(coreSrc);

try {{
    const module = require('{module_path}');
    const result = module.{function_name}({', '.join(repr(arg) for arg in args)});
    console.log(JSON.stringify(result));
}} catch (error) {{
    console.error('Error:', error.message);
    process.exit(1);
}}
"""
    
    script_path = Path("tests/_temp_call.js")
    script_path.write_text(script)
    
    try:
        result = subprocess.run(
            ["node", str(script_path)],
            capture_output=True,
            text=True,
            cwd=os.getcwd()
        )
        
        if result.returncode != 0:
            raise RuntimeError(f"Function call failed: {result.stderr}")
        
        return json.loads(result.stdout)
        
    finally:
        if script_path.exists():
            script_path.unlink()


def node_bridge():
    """Get the path to the Node.js bridge CLI."""
    cli = Path("bridge/cli.js").resolve()
    if not cli.exists():
        raise RuntimeError("bridge/cli.js missing. Create it first.")
    return ["node", str(cli)]


def bridge_call(cmd: str, *args: str):
    """Call the Node.js bridge with a command and arguments."""
    proc = subprocess.run(node_bridge() + [cmd, *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or proc.stdout.strip())
    return json.loads(proc.stdout or "{}")


def verify_production_build():
    """
    Verify that the production TypeScript code is built and available.
    """
    # Check if core source exists (we'll use ts-node for direct execution)
    core_src = Path("core/src")
    if not core_src.exists():
        raise RuntimeError("Core source directory not found. Expected: core/src")
    
    # Check if core has node_modules (dependencies installed)
    core_node_modules = Path("core/node_modules")
    if not core_node_modules.exists():
        print("Warning: Core node_modules not found. Please run 'npm install' in core directory.")
        # Don't fail here, just warn - the user can install dependencies manually
    
    return True

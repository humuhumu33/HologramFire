# IPFS Lock Prevention Guide

This guide explains how to prevent and resolve IPFS daemon lock issues that can occur when the daemon doesn't shut down cleanly.

## Problem Description

The error `lock C:\Users\pavel\.ipfs\repo.lock: someone else has the lock` occurs when:
- A previous IPFS process didn't shut down cleanly
- The system crashed while IPFS was running
- Multiple IPFS instances were started simultaneously
- The lock file wasn't properly released

## Prevention Solutions

### 1. Use the IPFS Manager Scripts

We've created comprehensive PowerShell scripts to manage IPFS lifecycle:

#### IPFS Manager (`scripts/ipfs-manager.ps1`)
- **Purpose**: Complete IPFS daemon management
- **Features**: Start, stop, restart, status check, cleanup, health monitoring
- **Usage**: 
  ```powershell
  .\scripts\ipfs-manager.ps1 [start|stop|restart|status|cleanup|health]
  ```

#### IPFS Startup Script (`scripts/startup-ipfs.ps1`)
- **Purpose**: Safe IPFS initialization with automatic lock cleanup
- **Features**: Automatic stale lock detection and removal, health checks
- **Usage**:
  ```powershell
  .\scripts\startup-ipfs.ps1 [-Force] [-Quiet]
  ```

### 2. NPM Scripts Integration

The following npm scripts are now available:

```bash
# Start IPFS with lock cleanup
npm run ipfs:start

# Stop IPFS gracefully
npm run ipfs:stop

# Restart IPFS (stops and starts)
npm run ipfs:restart

# Check IPFS status and health
npm run ipfs:status

# Clean up stale locks and temp files
npm run ipfs:cleanup

# Run health check
npm run ipfs:health

# Safe startup with automatic lock handling
npm run ipfs:startup

# Force startup (restarts stuck processes)
npm run ipfs:startup:force
```

### 3. Best Practices

#### Always Use the Manager Scripts
Instead of running `ipfs daemon --init` directly, use:
```bash
npm run ipfs:startup
```

#### Graceful Shutdown
Always stop IPFS using:
```bash
npm run ipfs:stop
```

#### Before Development Work
Run a health check:
```bash
npm run ipfs:health
```

#### If Issues Persist
Use cleanup and force restart:
```bash
npm run ipfs:cleanup
npm run ipfs:startup:force
```

## Manual Resolution (If Needed)

If the automated scripts don't work, you can manually resolve the issue:

### 1. Check for Running Processes
```powershell
Get-Process | Where-Object {$_.ProcessName -like "*ipfs*"}
```

### 2. Stop All IPFS Processes
```powershell
Get-Process | Where-Object {$_.ProcessName -like "*ipfs*"} | Stop-Process -Force
```

### 3. Remove Lock File
```powershell
Remove-Item "$env:USERPROFILE\.ipfs\repo.lock" -Force
```

### 4. Restart IPFS
```powershell
ipfs daemon --init
```

## Script Features

### IPFS Manager Script Features
- **Process Detection**: Automatically detects running IPFS processes
- **Lock File Management**: Removes stale lock files safely
- **Graceful Shutdown**: Properly terminates IPFS processes
- **Health Monitoring**: Checks API connectivity and process status
- **Cleanup Utilities**: Removes temporary files and logs
- **Status Reporting**: Detailed status information with color-coded output

### Startup Script Features
- **Automatic Lock Cleanup**: Detects and removes stale locks
- **Health Verification**: Ensures IPFS is actually responding
- **Stuck Process Detection**: Identifies and handles stuck processes
- **Force Mode**: Option to restart stuck processes
- **Quiet Mode**: Minimal output for automation

## Integration with Development Workflow

### Pre-commit Hook (Optional)
You can add IPFS health checks to your development workflow:

```json
{
  "husky": {
    "hooks": {
      "pre-commit": "npm run ipfs:health"
    }
  }
}
```

### CI/CD Integration
For automated environments, use the quiet mode:
```bash
npm run ipfs:startup --quiet
```

## Troubleshooting

### Common Issues

1. **PowerShell Execution Policy**
   - Error: "execution of scripts is disabled"
   - Solution: The scripts use `-ExecutionPolicy Bypass` flag

2. **Permission Denied**
   - Error: Cannot remove lock file
   - Solution: Run PowerShell as Administrator

3. **IPFS Not Found**
   - Error: "ipfs is not recognized"
   - Solution: Ensure IPFS is installed and in PATH

4. **Port Already in Use**
   - Error: Port 5001 already in use
   - Solution: Use `npm run ipfs:cleanup` then restart

### Debug Mode
For detailed debugging, run the PowerShell scripts directly:
```powershell
.\scripts\ipfs-manager.ps1 status
.\scripts\startup-ipfs.ps1 -Force
```

## File Locations

- **IPFS Repository**: `%USERPROFILE%\.ipfs\`
- **Lock File**: `%USERPROFILE%\.ipfs\repo.lock`
- **Manager Script**: `scripts\ipfs-manager.ps1`
- **Startup Script**: `scripts\startup-ipfs.ps1`
- **Batch Wrappers**: `scripts\ipfs-manager.bat`, `scripts\startup-ipfs.bat`

## Summary

By using these scripts and following the best practices, you should never encounter the IPFS lock error again. The scripts provide:

1. **Prevention**: Automatic lock cleanup before starting
2. **Detection**: Health checks and status monitoring
3. **Recovery**: Automatic cleanup and restart capabilities
4. **Integration**: Easy npm script integration
5. **Reliability**: Graceful shutdown and startup procedures

Always use `npm run ipfs:startup` instead of `ipfs daemon --init` to ensure a smooth experience.

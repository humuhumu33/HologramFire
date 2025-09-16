# IPFS Startup Script - Automatically handles lock issues and starts IPFS
# This script should be run before any IPFS operations

param(
    [switch]$Force,
    [switch]$Quiet
)

$IPFS_REPO_PATH = "$env:USERPROFILE\.ipfs"
$LOCK_FILE = "$IPFS_REPO_PATH\repo.lock"
$IPFS_PROCESS_NAME = "ipfs"

function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    if (-not $Quiet) {
        Write-Host $Message -ForegroundColor $Color
    }
}

function Test-IPFSProcess {
    $processes = Get-Process | Where-Object {$_.ProcessName -like "*$IPFS_PROCESS_NAME*"}
    return $processes.Count -gt 0
}

function Test-IPFSAPI {
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:5001/api/v0/version" -TimeoutSec 3 -ErrorAction Stop
        return $response.StatusCode -eq 200
    }
    catch {
        return $false
    }
}

function Remove-StaleLock {
    if (Test-Path $LOCK_FILE) {
        Write-ColorOutput "Found stale IPFS lock file" "Yellow"
        try {
            Remove-Item $LOCK_FILE -Force
            Write-ColorOutput "Removed stale lock file" "Green"
            return $true
        }
        catch {
            Write-ColorOutput "Failed to remove lock file: $($_.Exception.Message)" "Red"
            return $false
        }
    }
    return $true
}

function Start-IPFSIfNeeded {
    # Check if IPFS is already running and healthy
    if ((Test-IPFSProcess) -and (Test-IPFSAPI)) {
        Write-ColorOutput "IPFS daemon is already running and healthy" "Green"
        return $true
    }
    
    # If IPFS process exists but API is not responding, it might be stuck
    if ((Test-IPFSProcess) -and -not (Test-IPFSAPI)) {
        Write-ColorOutput "IPFS process exists but API is not responding" "Yellow"
        if ($Force) {
            Write-ColorOutput "Force flag detected, stopping stuck process..." "Yellow"
            Get-Process | Where-Object {$_.ProcessName -like "*$IPFS_PROCESS_NAME*"} | Stop-Process -Force
            Start-Sleep -Seconds 2
        } else {
            Write-ColorOutput "Use -Force flag to restart stuck IPFS process" "Yellow"
            return $false
        }
    }
    
    # Remove stale lock if exists
    if (-not (Remove-StaleLock)) {
        return $false
    }
    
    # Start IPFS daemon
    Write-ColorOutput "Starting IPFS daemon..." "Cyan"
    try {
        Start-Process -FilePath "ipfs" -ArgumentList "daemon", "--init" -WindowStyle Hidden
        Start-Sleep -Seconds 3
        
        # Wait for IPFS to be ready
        $maxWait = 30
        $waited = 0
        while ($waited -lt $maxWait) {
            if ((Test-IPFSProcess) -and (Test-IPFSAPI)) {
                Write-ColorOutput "IPFS daemon started successfully" "Green"
                Write-ColorOutput "Web UI: http://localhost:5001/webui" "Blue"
                return $true
            }
            Start-Sleep -Seconds 1
            $waited++
        }
        
        Write-ColorOutput "IPFS daemon failed to start within $maxWait seconds" "Red"
        return $false
    }
    catch {
        Write-ColorOutput "Error starting IPFS daemon: $($_.Exception.Message)" "Red"
        return $false
    }
}

# Main execution
Write-ColorOutput "IPFS Startup Check" "Cyan"
Write-ColorOutput "==================" "Cyan"

$success = Start-IPFSIfNeeded

if ($success) {
    Write-ColorOutput "IPFS is ready for use" "Green"
    exit 0
} else {
    Write-ColorOutput "IPFS startup failed" "Red"
    exit 1
}
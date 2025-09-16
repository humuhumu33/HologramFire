# IPFS Manager Script - Prevents lock issues and manages IPFS daemon lifecycle
# Usage: .\scripts\ipfs-manager.ps1 [start|stop|restart|status|cleanup]

param(
    [Parameter(Position=0)]
    [ValidateSet("start", "stop", "restart", "status", "cleanup", "health")]
    [string]$Action = "start"
)

$IPFS_REPO_PATH = "$env:USERPROFILE\.ipfs"
$LOCK_FILE = "$IPFS_REPO_PATH\repo.lock"
$IPFS_PROCESS_NAME = "ipfs"

function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

function Test-IPFSProcess {
    $processes = Get-Process | Where-Object {$_.ProcessName -like "*$IPFS_PROCESS_NAME*"}
    return $processes.Count -gt 0
}

function Get-IPFSProcess {
    return Get-Process | Where-Object {$_.ProcessName -like "*$IPFS_PROCESS_NAME*"}
}

function Remove-StaleLock {
    if (Test-Path $LOCK_FILE) {
        Write-ColorOutput "Found stale lock file, removing..." "Yellow"
        try {
            Remove-Item $LOCK_FILE -Force
            Write-ColorOutput "✓ Stale lock file removed successfully" "Green"
            return $true
        }
        catch {
            Write-ColorOutput "✗ Failed to remove lock file: $($_.Exception.Message)" "Red"
            return $false
        }
    }
    return $true
}

function Start-IPFSDaemon {
    Write-ColorOutput "Starting IPFS daemon..." "Cyan"
    
    # Check for existing processes
    if (Test-IPFSProcess) {
        Write-ColorOutput "IPFS process already running. Use 'restart' to restart it." "Yellow"
        return $false
    }
    
    # Remove stale lock if exists
    if (-not (Remove-StaleLock)) {
        return $false
    }
    
    # Start IPFS daemon
    try {
        Write-ColorOutput "Initializing IPFS daemon..." "Cyan"
        Start-Process -FilePath "ipfs" -ArgumentList "daemon", "--init" -WindowStyle Hidden
        Start-Sleep -Seconds 3
        
        if (Test-IPFSProcess) {
            Write-ColorOutput "✓ IPFS daemon started successfully" "Green"
            Write-ColorOutput "Web UI available at: http://localhost:5001/webui" "Blue"
            return $true
        } else {
            Write-ColorOutput "✗ IPFS daemon failed to start" "Red"
            return $false
        }
    }
    catch {
        Write-ColorOutput "✗ Error starting IPFS daemon: $($_.Exception.Message)" "Red"
        return $false
    }
}

function Stop-IPFSDaemon {
    Write-ColorOutput "Stopping IPFS daemon..." "Cyan"
    
    $processes = Get-IPFSProcess
    if ($processes.Count -eq 0) {
        Write-ColorOutput "No IPFS processes found" "Yellow"
        return $true
    }
    
    try {
        foreach ($process in $processes) {
            Write-ColorOutput "Stopping process ID: $($process.Id)" "Yellow"
            Stop-Process -Id $process.Id -Force
        }
        
        # Wait for processes to terminate
        $timeout = 10
        $elapsed = 0
        while ((Test-IPFSProcess) -and $elapsed -lt $timeout) {
            Start-Sleep -Seconds 1
            $elapsed++
        }
        
        if (Test-IPFSProcess) {
            Write-ColorOutput "✗ Some IPFS processes did not stop gracefully" "Red"
            return $false
        } else {
            Write-ColorOutput "✓ IPFS daemon stopped successfully" "Green"
            return $true
        }
    }
    catch {
        Write-ColorOutput "✗ Error stopping IPFS daemon: $($_.Exception.Message)" "Red"
        return $false
    }
}

function Get-IPFSStatus {
    Write-ColorOutput "IPFS Status Check" "Cyan"
    Write-ColorOutput "=================" "Cyan"
    
    $processes = Get-IPFSProcess
    if ($processes.Count -gt 0) {
        Write-ColorOutput "✓ IPFS daemon is running" "Green"
        foreach ($process in $processes) {
            Write-ColorOutput "  Process ID: $($process.Id)" "White"
            Write-ColorOutput "  CPU Time: $($process.TotalProcessorTime)" "White"
            Write-ColorOutput "  Memory: $([math]::Round($process.WorkingSet64 / 1MB, 2)) MB" "White"
        }
    } else {
        Write-ColorOutput "✗ IPFS daemon is not running" "Red"
    }
    
    if (Test-Path $LOCK_FILE) {
        Write-ColorOutput "⚠ Lock file exists: $LOCK_FILE" "Yellow"
    } else {
        Write-ColorOutput "✓ No lock file found" "Green"
    }
    
    # Test IPFS connectivity
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:5001/api/v0/version" -TimeoutSec 5 -ErrorAction Stop
        if ($response.StatusCode -eq 200) {
            Write-ColorOutput "✓ IPFS API is responding" "Green"
        }
    }
    catch {
        Write-ColorOutput "✗ IPFS API is not responding" "Red"
    }
}

function Invoke-IPFSCleanup {
    Write-ColorOutput "Performing IPFS cleanup..." "Cyan"
    
    # Stop any running processes
    if (Test-IPFSProcess) {
        Write-ColorOutput "Stopping running IPFS processes..." "Yellow"
        Stop-IPFSDaemon | Out-Null
    }
    
    # Remove lock file
    Remove-StaleLock | Out-Null
    
    # Clean up any temporary files
    $tempFiles = @(
        "$IPFS_REPO_PATH\temp\*",
        "$IPFS_REPO_PATH\logs\*"
    )
    
    foreach ($pattern in $tempFiles) {
        if (Test-Path $pattern) {
            try {
                Remove-Item $pattern -Recurse -Force -ErrorAction SilentlyContinue
                Write-ColorOutput "✓ Cleaned up temporary files" "Green"
            }
            catch {
                Write-ColorOutput "⚠ Could not clean some temporary files" "Yellow"
            }
        }
    }
    
    Write-ColorOutput "✓ IPFS cleanup completed" "Green"
}

function Test-IPFSHealth {
    Write-ColorOutput "IPFS Health Check" "Cyan"
    Write-ColorOutput "=================" "Cyan"
    
    $healthy = $true
    
    # Check if daemon is running
    if (-not (Test-IPFSProcess)) {
        Write-ColorOutput "✗ IPFS daemon is not running" "Red"
        $healthy = $false
    }
    
    # Check for lock file
    if (Test-Path $LOCK_FILE) {
        Write-ColorOutput "⚠ Stale lock file detected" "Yellow"
        $healthy = $false
    }
    
    # Test API connectivity
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:5001/api/v0/version" -TimeoutSec 5 -ErrorAction Stop
        if ($response.StatusCode -ne 200) {
            Write-ColorOutput "✗ IPFS API not responding correctly" "Red"
            $healthy = $false
        }
    }
    catch {
        Write-ColorOutput "✗ IPFS API not accessible" "Red"
        $healthy = $false
    }
    
    if ($healthy) {
        Write-ColorOutput "✓ IPFS is healthy" "Green"
        return $true
    } else {
        Write-ColorOutput "✗ IPFS health check failed" "Red"
        return $false
    }
}

# Main execution
switch ($Action.ToLower()) {
    "start" {
        Start-IPFSDaemon
    }
    "stop" {
        Stop-IPFSDaemon
    }
    "restart" {
        Write-ColorOutput "Restarting IPFS daemon..." "Cyan"
        if (Stop-IPFSDaemon) {
            Start-Sleep -Seconds 2
            Start-IPFSDaemon
        }
    }
    "status" {
        Get-IPFSStatus
    }
    "cleanup" {
        Invoke-IPFSCleanup
    }
    "health" {
        Test-IPFSHealth
    }
    default {
        Write-ColorOutput "Usage: .\scripts\ipfs-manager.ps1 [start|stop|restart|status|cleanup|health]" "Yellow"
    }
}

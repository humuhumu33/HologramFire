#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Windows development shell for Hologram pipeline.
    
.DESCRIPTION
    Opens a pre-configured PowerShell session with:
    - Repo mapped to X: drive (short paths)
    - Pytest temp/cache in short directories
    - PNPM store optimized
    - All environment variables set
    
    Use this for daily development to avoid Windows path-length issues.
    
.EXAMPLE
    .\tools\windows_dev_shell.ps1
    # Opens configured shell in current repo
    
.EXAMPLE
    .\tools\windows_dev_shell.ps1 -KeepExisting
    # Keeps existing X: mapping if it exists
#>

param(
    [switch]$KeepExisting
)

# Colors for output
$ErrorColor = "Red"
$SuccessColor = "Green" 
$InfoColor = "Cyan"
$WarningColor = "Yellow"

function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

Write-ColorOutput "🚀 Starting Hologram Windows dev shell..." $InfoColor

# Function to find a free drive letter
function Get-FreeDriveLetter {
    $used = (Get-PSDrive -PSProvider FileSystem).Name
    foreach ($c in @('X','Y','Z','W','V')) { 
        if ($used -notcontains $c) { 
            return $c 
        } 
    }
    return $null
}

try {
    # Get current repo path
    $repoPath = (Resolve-Path .).Path
    Write-ColorOutput "   Repo: $repoPath" $InfoColor
    
    # Find a free drive letter
    $drive = Get-FreeDriveLetter
    if (-not $drive) {
        Write-ColorOutput "   ❌ No free drive letter found (X, Y, Z, W, V all in use)" $ErrorColor
        Write-ColorOutput "      Please free up a drive letter or use manual subst command" $ErrorColor
        exit 1
    }
    
    Write-ColorOutput "   Using drive letter: $drive`:" $InfoColor
    
    # Check if the drive is already mapped
    $existingMapping = $null
    try {
        $existingMapping = (subst | Where-Object { $_ -match "^$drive`:" }).Trim()
    } catch { }
    
    if ($existingMapping -and -not $KeepExisting) {
        Write-ColorOutput "   Removing existing $drive`: mapping..." $InfoColor
        subst "$drive`:" /D | Out-Null
    } elseif ($existingMapping -and $KeepExisting) {
        Write-ColorOutput "   Using existing $drive`: mapping: $existingMapping" $InfoColor
    }
    
    # Create drive mapping if needed
    if (-not $existingMapping -or -not $KeepExisting) {
        Write-ColorOutput "   Mapping repo to $drive`: drive..." $InfoColor
        subst "$drive`:" $repoPath
        Write-ColorOutput "   ✅ Repo mapped to $drive`:\" $SuccessColor
    }
    
    # Ensure short temp directories exist
    Write-ColorOutput "   Ensuring temp directories..." $InfoColor
    New-Item -ItemType Directory -Force C:\t\pt | Out-Null
    New-Item -ItemType Directory -Force C:\t\pc | Out-Null
    
    # Set environment variables
    Write-ColorOutput "   Setting environment variables..." $InfoColor
    $env:PYTEST_ADDOPTS = '--basetemp=C:\t\pt -o cache_dir=C:\t\pc'
    $env:TMP = 'C:\t\tooltmp'
    $env:TEMP = 'C:\t\tooltmp'
    
    # Create tool temp directory
    New-Item -ItemType Directory -Force C:\t\tooltmp | Out-Null
    
    # Change to mapped drive
    Set-Location "$drive`:\"
    Write-ColorOutput "   ✅ Changed to $drive`:\ drive" $SuccessColor
    
    # Check PNPM store
    if (Get-Command pnpm -ErrorAction SilentlyContinue) {
        $pnpmStore = pnpm config get store-dir
        if ($pnpmStore -notlike "*C:\pnpm-store*") {
            Write-ColorOutput "   Configuring PNPM store..." $InfoColor
            pnpm config set store-dir C:\pnpm-store
        }
    }
    
    Write-ColorOutput "`n✅ Dev shell ready!" $SuccessColor
    Write-ColorOutput "`n📋 Available commands:" $InfoColor
    Write-ColorOutput "  python -m pytest -m 'phase6_perf or phase8_e2e' -q" $InfoColor
    Write-ColorOutput "  python scripts/aggregate_reports.py" $InfoColor
    Write-ColorOutput "  python scripts/check_perf_budget.py" $InfoColor
    Write-ColorOutput "  python scripts/summarize_e2e.py" $InfoColor
    Write-ColorOutput "  pnpm -C core build" $InfoColor
    Write-ColorOutput "`nTip: Use subst X: /D to remove the drive mapping when done" $WarningColor
    
    # Show current status
    Write-ColorOutput "`n🔥 Hologram Dev Shell Active!" $SuccessColor
    Write-ColorOutput "   Working directory: $drive`:\ (mapped to repo)" $InfoColor
    Write-ColorOutput "   Pytest temp: C:\t\pt" $InfoColor
    Write-ColorOutput "   Pytest cache: C:\t\pc" $InfoColor
    Write-ColorOutput "   PNPM store: C:\pnpm-store" $InfoColor
    Write-ColorOutput "`n   Ready for development!" $InfoColor
    
} catch {
    Write-ColorOutput "❌ Failed to start dev shell: $($_.Exception.Message)" $ErrorColor
    exit 1
}
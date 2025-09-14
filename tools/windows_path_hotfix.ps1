#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Windows path-length hotfix for Hologram pipeline development.
    
.DESCRIPTION
    Fixes Windows MAX_PATH (260 char) issues that can break pytest and Node.js tools
    when working with deeply nested project structures.
    
    Run this script once per machine (admin required for OS-level changes).
    Then use the dev shell script for daily development.
    
.PARAMETER AdminOnly
    Only run the admin-required parts (OS registry + Git config)
    
.PARAMETER UserOnly  
    Only run the user-level parts (subst, env vars, pnpm config)
    
.EXAMPLE
    .\tools\windows_path_hotfix.ps1
    # Run everything (requires admin for first part)
    
.EXAMPLE
    .\tools\windows_path_hotfix.ps1 -AdminOnly
    # Just the OS + Git changes (run as admin)
    
.EXAMPLE
    .\tools\windows_path_hotfix.ps1 -UserOnly
    # Just the user-level changes (run in repo)
#>

param(
    [switch]$AdminOnly,
    [switch]$UserOnly
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

function Test-IsAdmin {
    $currentUser = [Security.Principal.WindowsIdentity]::GetCurrent()
    $principal = New-Object Security.Principal.WindowsPrincipal($currentUser)
    return $principal.IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
}

# Admin-required changes
if (-not $UserOnly) {
    Write-ColorOutput "🔧 Applying admin-level Windows path fixes..." $InfoColor
    
    if (-not (Test-IsAdmin)) {
        Write-ColorOutput "❌ Admin privileges required for OS-level changes." $ErrorColor
        Write-ColorOutput "   Run PowerShell as Administrator, or use -UserOnly flag" $WarningColor
        exit 1
    }
    
    try {
        # 1) Enable long paths in Windows
        Write-ColorOutput "   Enabling Windows long paths..." $InfoColor
        New-ItemProperty -Path "HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem" `
            -Name LongPathsEnabled -Value 1 -PropertyType DWord -Force | Out-Null
        Write-ColorOutput "   ✅ Long paths enabled" $SuccessColor
        
        # 2) Configure Git for long paths
        Write-ColorOutput "   Configuring Git for long paths..." $InfoColor
        git config --system core.longpaths true
        Write-ColorOutput "   ✅ Git long paths configured" $SuccessColor
        
        Write-ColorOutput "✅ Admin-level changes complete!" $SuccessColor
        Write-ColorOutput "   Restart PowerShell for changes to take effect." $WarningColor
        
    } catch {
        Write-ColorOutput "❌ Failed to apply admin changes: $($_.Exception.Message)" $ErrorColor
        exit 1
    }
}

# User-level changes
if (-not $AdminOnly) {
    Write-ColorOutput "🔧 Applying user-level path optimizations..." $InfoColor
    
    try {
        # 3) Create short drive mapping
        $repoPath = (Resolve-Path .).Path
        Write-ColorOutput "   Mapping repo to X: drive..." $InfoColor
        Write-ColorOutput "   Repo path: $repoPath" $InfoColor
        
        # Remove existing X: mapping if it exists
        try { subst X: /D | Out-Null } catch { }
        
        # Create new mapping
        subst X: $repoPath
        Write-ColorOutput "   ✅ Repo mapped to X:\" $SuccessColor
        
        # 4) Create short temp directories
        Write-ColorOutput "   Creating short temp directories..." $InfoColor
        New-Item -ItemType Directory -Force C:\t\pt | Out-Null
        New-Item -ItemType Directory -Force C:\t\pc | Out-Null
        Write-ColorOutput "   ✅ Temp dirs created: C:\t\pt, C:\t\pc" $SuccessColor
        
        # 5) Set pytest environment variables
        Write-ColorOutput "   Configuring pytest for short paths..." $InfoColor
        $env:PYTEST_ADDOPTS = '--basetemp=C:\t\pt -o cache_dir=C:\t\pc'
        Write-ColorOutput "   ✅ Pytest configured" $SuccessColor
        
        # 6) Configure PNPM for shorter paths
        Write-ColorOutput "   Configuring PNPM store location..." $InfoColor
        if (Get-Command pnpm -ErrorAction SilentlyContinue) {
            pnpm config set store-dir C:\pnpm-store
            pnpm config set shamefully-hoist false
            pnpm store prune | Out-Null
            Write-ColorOutput "   ✅ PNPM store configured" $SuccessColor
        } else {
            Write-ColorOutput "   ⚠️  PNPM not found, skipping store config" $WarningColor
        }
        
        # 7) Change to X: drive
        Set-Location X:\
        Write-ColorOutput "   ✅ Changed to X:\ drive" $SuccessColor
        
        Write-ColorOutput "✅ User-level changes complete!" $SuccessColor
        
    } catch {
        Write-ColorOutput "❌ Failed to apply user changes: $($_.Exception.Message)" $ErrorColor
        exit 1
    }
}

Write-ColorOutput "`n🎉 Windows path hotfix complete!" $SuccessColor
Write-ColorOutput "`nNext steps:" $InfoColor
Write-ColorOutput "  1. Restart PowerShell if you ran admin changes" $InfoColor
Write-ColorOutput "  2. Use '.\tools\windows_dev_shell.ps1' for daily development" $InfoColor
Write-ColorOutput "  3. Run tests from X:\ drive: python -m pytest -m 'phase6_perf or phase8_e2e' -q" $InfoColor

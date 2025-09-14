#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Windows Dev Shell with banner - shows active environment settings.
    
.DESCRIPTION
    Opens a new PowerShell window with Hologram optimizations and displays
    a banner showing the active drive, environment variables, and settings.
#>

# Colors
$SuccessColor = "Green"
$InfoColor = "Cyan"
$WarningColor = "Yellow"

function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

# Get repo path
$repoPath = (Resolve-Path .).Path

# Find free drive letter
function Get-FreeDriveLetter {
    $used = (Get-PSDrive -PSProvider FileSystem).Name
    foreach ($c in @('X','Y','Z','W','V')) { 
        if ($used -notcontains $c) { return $c } 
    }
    return $null
}

$drive = Get-FreeDriveLetter
if (-not $drive) {
    Write-ColorOutput "❌ No free drive letter found" $WarningColor
    exit 1
}

# Setup environment
subst "$drive`:" $repoPath | Out-Null
$env:PYTEST_ADDOPTS = '--basetemp=C:\t\pt -o cache_dir=C:\t\pc'
$env:TMP = 'C:\t\tooltmp'
$env:TEMP = 'C:\t\tooltmp'
New-Item -ItemType Directory -Force C:\t\pt,C:\t\pc,C:\t\tooltmp | Out-Null

# Configure PNPM
if (Get-Command pnpm -ErrorAction SilentlyContinue) {
    pnpm config set store-dir C:\pnpm-store | Out-Null
    pnpm config set shamefully-hoist false | Out-Null
}

# Create banner script
$bannerScript = @"
Write-Host "🔥 Hologram Windows Dev Shell" -ForegroundColor Green
Write-Host "================================" -ForegroundColor Green
Write-Host "Drive: $drive`:\ (mapped to repo)" -ForegroundColor Cyan
Write-Host "Pytest temp: C:\t\pt" -ForegroundColor Cyan
Write-Host "Pytest cache: C:\t\pc" -ForegroundColor Cyan
Write-Host "PNPM store: C:\pnpm-store" -ForegroundColor Cyan
Write-Host "TMP/TEMP: C:\t\tooltmp" -ForegroundColor Cyan
Write-Host ""
Write-Host "Ready for development!" -ForegroundColor Green
Write-Host ""
"@

# Start new PowerShell window
Start-Process pwsh -ArgumentList "-NoExit", "-Command", "Set-Location '$drive`:\'; $bannerScript"

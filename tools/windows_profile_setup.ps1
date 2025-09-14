#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Set up PowerShell profile for automatic Windows path-length optimization.
    
.DESCRIPTION
    Adds Hologram-specific path optimizations to the user's PowerShell profile
    so they're automatically applied in every new PowerShell session.
    
    This makes the Windows hotfix "stick" so developers don't have to think about it.
    
.EXAMPLE
    .\tools\windows_profile_setup.ps1
    # Add Hologram optimizations to PowerShell profile
    
.EXAMPLE
    .\tools\windows_profile_setup.ps1 -Remove
    # Remove Hologram optimizations from PowerShell profile
#>

param(
    [switch]$Remove
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

# Get the profile path
$profilePath = $PROFILE.CurrentUserAllHosts
$profileDir = Split-Path $profilePath -Parent

Write-ColorOutput "🔧 PowerShell Profile Setup for Hologram" $InfoColor
Write-ColorOutput "   Profile: $profilePath" $InfoColor
Write-ColorOutput ""

# Check and set execution policy if needed
Write-ColorOutput "   Checking execution policy..." $InfoColor
$currentPolicy = Get-ExecutionPolicy -Scope CurrentUser
if ($currentPolicy -eq "Restricted") {
    Write-ColorOutput "   Setting execution policy to RemoteSigned..." $InfoColor
    try {
        Set-ExecutionPolicy -Scope CurrentUser -ExecutionPolicy RemoteSigned -Force
        Write-ColorOutput "   ✅ Execution policy updated" $SuccessColor
    } catch {
        Write-ColorOutput "   ⚠️  Could not set execution policy: $($_.Exception.Message)" $WarningColor
    }
} else {
    Write-ColorOutput "   ✅ Execution policy is permissive ($currentPolicy)" $SuccessColor
}

# Ensure profile directory exists
if (-not (Test-Path $profileDir)) {
    Write-ColorOutput "   Creating profile directory..." $InfoColor
    New-Item -ItemType Directory -Force $profileDir | Out-Null
}

# Function to find a free drive letter
$driveFunction = @"
function Get-FreeDriveLetter {
    `$used = (Get-PSDrive -PSProvider FileSystem).Name
    foreach (`$c in @('X','Y','Z','W','V')) { 
        if (`$used -notcontains `$c) { 
            return `$c 
        } 
    }
    return `$null
}
"@

# Hologram optimization code
$hologramCode = @"
# Hologram Windows path-length optimizations
# Added by tools/windows_profile_setup.ps1

$driveFunction

# Auto-map current repo to a free drive if we're in a Hologram repo
if ((Get-Location).Path -like "*HologramFire*") {
    `$drive = Get-FreeDriveLetter
    if (`$drive -and -not (Get-PSDrive -Name `$drive -ErrorAction SilentlyContinue)) {
        try {
            subst "`$drive`:" (Resolve-Path .) | Out-Null
            Set-Location "`$drive`:\"
            Write-Host "🔥 Hologram: Mapped repo to `$drive`:\ drive" -ForegroundColor Green
        } catch {
            # Silently fail if subst fails
        }
    }
}

# Set pytest environment variables for short paths
`$env:PYTEST_ADDOPTS = '--basetemp=C:\t\pt -o cache_dir=C:\t\pc'

# Ensure short temp directories exist
New-Item -ItemType Directory -Force C:\t\pt, C:\t\pc, C:\t\tooltmp | Out-Null

# Configure PNPM store for shorter paths (if PNPM is available)
if (Get-Command pnpm -ErrorAction SilentlyContinue) {
    try {
        `$currentStore = pnpm config get store-dir 2>`$null
        if (`$currentStore -notlike "*C:\pnpm-store*") {
            pnpm config set store-dir C:\pnpm-store | Out-Null
            pnpm config set shamefully-hoist false | Out-Null
        }
    } catch {
        # Silently fail if PNPM config fails
    }
}

# Set short temp environment variables
`$env:TMP = 'C:\t\tooltmp'
`$env:TEMP = 'C:\t\tooltmp'
"@

if ($Remove) {
    Write-ColorOutput "🗑️  Removing Hologram optimizations from profile..." $InfoColor
    
    if (Test-Path $profilePath) {
        $content = Get-Content $profilePath -Raw
        if ($content -match "# Hologram Windows path-length optimizations") {
            # Remove the Hologram section
            $lines = Get-Content $profilePath
            $newLines = @()
            $inHologramSection = $false
            
            foreach ($line in $lines) {
                if ($line -match "# Hologram Windows path-length optimizations") {
                    $inHologramSection = $true
                    continue
                }
                if ($inHologramSection -and $line -match "^# Added by tools/windows_profile_setup.ps1") {
                    $inHologramSection = $false
                    continue
                }
                if (-not $inHologramSection) {
                    $newLines += $line
                }
            }
            
            $newLines | Set-Content $profilePath
            Write-ColorOutput "   ✅ Hologram optimizations removed from profile" $SuccessColor
        } else {
            Write-ColorOutput "   ℹ️  No Hologram optimizations found in profile" $InfoColor
        }
    } else {
        Write-ColorOutput "   ℹ️  Profile file doesn't exist" $InfoColor
    }
} else {
    Write-ColorOutput "➕ Adding Hologram optimizations to profile..." $InfoColor
    
    # Check if Hologram code is already in the profile
    if (Test-Path $profilePath) {
        $content = Get-Content $profilePath -Raw
        if ($content -match "# Hologram Windows path-length optimizations") {
            Write-ColorOutput "   ℹ️  Hologram optimizations already in profile" $InfoColor
            return
        }
    }
    
    # Add Hologram code to profile
    $hologramCode | Add-Content $profilePath
    Write-ColorOutput "   ✅ Hologram optimizations added to profile" $SuccessColor
}

Write-ColorOutput ""
Write-ColorOutput "📋 What this does:" $InfoColor
Write-ColorOutput "  • Auto-maps Hologram repos to X:\ drive" $InfoColor
Write-ColorOutput "  • Sets pytest to use short temp directories" $InfoColor
Write-ColorOutput "  • Configures PNPM store for shorter paths" $InfoColor
Write-ColorOutput "  • Sets short temp environment variables" $InfoColor

Write-ColorOutput ""
Write-ColorOutput "🔄 To apply changes:" $InfoColor
Write-ColorOutput "  • Restart PowerShell, or" $InfoColor
Write-ColorOutput "  • Run: . `$PROFILE" $InfoColor

Write-ColorOutput ""
Write-ColorOutput "🗑️  To remove later:" $InfoColor
Write-ColorOutput "  • Run: .\tools\windows_profile_setup.ps1 -Remove" $InfoColor

#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Cleanup and undo Windows path-length hotfix changes.
    
.DESCRIPTION
    Removes drive mappings, resets environment variables, and cleans up
    temporary directories created by the Windows hotfix kit.
    
    Use this when you're done with development or want to reset your environment.
    
.EXAMPLE
    .\tools\windows_cleanup.ps1
    # Remove all hotfix changes
    
.EXAMPLE
    .\tools\windows_cleanup.ps1 -KeepTempDirs
    # Remove mappings but keep temp directories
#>

param(
    [switch]$KeepTempDirs
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

Write-ColorOutput "🧹 Windows Path-Length Hotfix Cleanup" $InfoColor
Write-ColorOutput ""

# 1) Remove X: drive mapping
Write-ColorOutput "1️⃣ Removing X: drive mapping..." $InfoColor
try {
    $substOutput = subst 2>$null
    $xMapping = $substOutput | Where-Object { $_ -match "^X:" }
    if ($xMapping) {
        subst X: /D | Out-Null
        Write-ColorOutput "   ✅ Removed X: drive mapping" $SuccessColor
    } else {
        Write-ColorOutput "   ℹ️  X: drive not mapped" $InfoColor
    }
} catch {
    Write-ColorOutput "   ❌ Failed to remove X: drive mapping: $($_.Exception.Message)" $ErrorColor
}

# 2) Reset environment variables
Write-ColorOutput "2️⃣ Resetting environment variables..." $InfoColor
$env:PYTEST_ADDOPTS = $null
$env:TMP = $null
$env:TEMP = $null
Write-ColorOutput "   ✅ Environment variables reset" $SuccessColor

# 3) Clean up temp directories
if (-not $KeepTempDirs) {
    Write-ColorOutput "3️⃣ Cleaning up temp directories..." $InfoColor
    $tempDirs = @("C:\t\pt", "C:\t\pc", "C:\t\tooltmp")
    foreach ($dir in $tempDirs) {
        if (Test-Path $dir) {
            try {
                Remove-Item $dir -Recurse -Force
                Write-ColorOutput "   ✅ Removed $dir" $SuccessColor
            } catch {
                Write-ColorOutput "   ⚠️  Could not remove $dir (may be in use)" $WarningColor
            }
        }
    }
    
    # Try to remove the parent C:\t directory if empty
    if (Test-Path "C:\t") {
        try {
            $items = Get-ChildItem "C:\t" -ErrorAction SilentlyContinue
            if (-not $items) {
                Remove-Item "C:\t" -Force
                Write-ColorOutput "   ✅ Removed C:\t directory" $SuccessColor
            }
        } catch {
            # Silently ignore if we can't remove it
        }
    }
} else {
    Write-ColorOutput "3️⃣ Keeping temp directories (use -KeepTempDirs flag)" $InfoColor
}

# 4) Reset PNPM store location (optional)
Write-ColorOutput "4️⃣ Resetting PNPM store location..." $InfoColor
if (Get-Command pnpm -ErrorAction SilentlyContinue) {
    try {
        $currentStore = pnpm config get store-dir 2>$null
        if ($currentStore -like "*C:\pnpm-store*") {
            pnpm config delete store-dir
            Write-ColorOutput "   ✅ PNPM store location reset to default" $SuccessColor
        } else {
            Write-ColorOutput "   ℹ️  PNPM store already at default location" $InfoColor
        }
    } catch {
        Write-ColorOutput "   ⚠️  Could not reset PNPM store location" $WarningColor
    }
} else {
    Write-ColorOutput "   ℹ️  PNPM not installed, skipping store reset" $InfoColor
}

# 5) Check for PowerShell profile cleanup
Write-ColorOutput "5️⃣ Checking PowerShell profile..." $InfoColor
$profilePath = $PROFILE.CurrentUserAllHosts
if (Test-Path $profilePath) {
    $content = Get-Content $profilePath -Raw
    if ($content -match "# Hologram Windows path-length optimizations") {
        Write-ColorOutput "   ⚠️  Hologram optimizations found in PowerShell profile" $WarningColor
        Write-ColorOutput "      Run: .\tools\windows_profile_setup.ps1 -Remove" $WarningColor
    } else {
        Write-ColorOutput "   ✅ No Hologram optimizations in PowerShell profile" $SuccessColor
    }
} else {
    Write-ColorOutput "   ℹ️  PowerShell profile doesn't exist" $InfoColor
}

Write-ColorOutput ""
Write-ColorOutput "✅ Cleanup complete!" $SuccessColor
Write-ColorOutput ""
Write-ColorOutput "📋 What was removed:" $InfoColor
Write-ColorOutput "  • X: drive mapping" $InfoColor
Write-ColorOutput "  • Pytest environment variables" $InfoColor
Write-ColorOutput "  • Short temp environment variables" $InfoColor
if (-not $KeepTempDirs) {
    Write-ColorOutput "  • Temporary directories (C:\t\*)" $InfoColor
}
Write-ColorOutput "  • PNPM store location (reset to default)" $InfoColor

Write-ColorOutput ""
Write-ColorOutput "🔄 To reapply hotfix later:" $InfoColor
Write-ColorOutput "  • Run: .\tools\windows_path_hotfix.ps1" $InfoColor
Write-ColorOutput "  • Or: .\tools\windows_dev_shell.ps1" $InfoColor

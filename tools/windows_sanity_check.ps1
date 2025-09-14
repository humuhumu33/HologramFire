#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Sanity checks for Windows path-length hotfix installation.
    
.DESCRIPTION
    Verifies that the Windows hotfix kit is properly installed and working.
    Run this after running windows_path_hotfix.ps1 to confirm everything is set up correctly.
    
.EXAMPLE
    .\tools\windows_sanity_check.ps1
    # Run all sanity checks
#>

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

Write-ColorOutput "🔍 Running Windows path-length hotfix sanity checks..." $InfoColor
Write-ColorOutput ""

$allChecksPassed = $true

# 1) Check long path support
Write-ColorOutput "1️⃣ Checking Windows long path support..." $InfoColor
try {
    $longPathsEnabled = Get-ItemProperty -Path "HKLM:\System\CurrentControlSet\Control\FileSystem" -Name LongPathsEnabled -ErrorAction SilentlyContinue
    if ($longPathsEnabled -and $longPathsEnabled.LongPathsEnabled -eq 1) {
        Write-ColorOutput "   ✅ Long paths enabled in Windows registry" $SuccessColor
    } else {
        Write-ColorOutput "   ⚠️  Long paths not enabled (may need admin privileges)" $WarningColor
        if (-not (Test-IsAdmin)) {
            Write-ColorOutput "      Run as admin: .\tools\windows_path_hotfix.ps1 -AdminOnly" $WarningColor
        }
    }
} catch {
    Write-ColorOutput "   ❌ Could not check long paths registry setting" $ErrorColor
    $allChecksPassed = $false
}

# 2) Check Git long paths setting
Write-ColorOutput "2️⃣ Checking Git long paths configuration..." $InfoColor
try {
    $gitLongPaths = git config --get core.longpaths 2>$null
    if ($gitLongPaths -eq "true") {
        Write-ColorOutput "   ✅ Git long paths enabled" $SuccessColor
    } else {
        Write-ColorOutput "   ⚠️  Git long paths not configured" $WarningColor
        Write-ColorOutput "      Run: git config --system core.longpaths true" $WarningColor
    }
} catch {
    Write-ColorOutput "   ❌ Could not check Git configuration" $ErrorColor
    $allChecksPassed = $false
}

# 3) Check X: drive mapping
Write-ColorOutput "3️⃣ Checking X: drive mapping..." $InfoColor
try {
    $substOutput = subst 2>$null
    $xMapping = $substOutput | Where-Object { $_ -match "^X:" }
    if ($xMapping) {
        Write-ColorOutput "   ✅ X: drive mapped: $xMapping" $SuccessColor
    } else {
        Write-ColorOutput "   ⚠️  X: drive not mapped" $WarningColor
        Write-ColorOutput "      Run: .\tools\windows_dev_shell.ps1" $WarningColor
    }
} catch {
    Write-ColorOutput "   ❌ Could not check drive mappings" $ErrorColor
    $allChecksPassed = $false
}

# 4) Check pytest environment variables
Write-ColorOutput "4️⃣ Checking pytest environment variables..." $InfoColor
if ($env:PYTEST_ADDOPTS) {
    Write-ColorOutput "   ✅ PYTEST_ADDOPTS set: $env:PYTEST_ADDOPTS" $SuccessColor
} else {
    Write-ColorOutput "   ⚠️  PYTEST_ADDOPTS not set" $WarningColor
    Write-ColorOutput "      Run: .\tools\windows_dev_shell.ps1" $WarningColor
}

# 5) Check short temp directories
Write-ColorOutput "5️⃣ Checking short temp directories..." $InfoColor
$tempDirs = @("C:\t\pt", "C:\t\pc", "C:\t\tooltmp")
foreach ($dir in $tempDirs) {
    if (Test-Path $dir) {
        Write-ColorOutput "   ✅ $dir exists" $SuccessColor
    } else {
        Write-ColorOutput "   ⚠️  $dir missing" $WarningColor
        Write-ColorOutput "      Run: .\tools\windows_dev_shell.ps1" $WarningColor
    }
}

# 6) Test path length capability
Write-ColorOutput "6️⃣ Testing path length capability..." $InfoColor
try {
    # Create a very deep path (>260 chars)
    $deepPath = "X:\test\" + ("verylongsubdirectoryname\" * 40) + "testfile.txt"
    
    # Ensure the directory structure exists
    $deepDir = Split-Path $deepPath -Parent
    New-Item -ItemType Directory -Force $deepDir | Out-Null
    
    # Try to create a file at the deep path
    "test content" | Out-File -FilePath $deepPath -Encoding UTF8
    
    if (Test-Path $deepPath) {
        Write-ColorOutput "   ✅ Successfully created file at path >260 chars" $SuccessColor
        Write-ColorOutput "      Path length: $($deepPath.Length) characters" $InfoColor
        
        # Clean up
        Remove-Item $deepPath -Force
        Remove-Item $deepDir -Recurse -Force
    } else {
        Write-ColorOutput "   ❌ Failed to create file at deep path" $ErrorColor
        $allChecksPassed = $false
    }
} catch {
    Write-ColorOutput "   ❌ Path length test failed: $($_.Exception.Message)" $ErrorColor
    $allChecksPassed = $false
}

# 7) Check PNPM store configuration
Write-ColorOutput "7️⃣ Checking PNPM store configuration..." $InfoColor
if (Get-Command pnpm -ErrorAction SilentlyContinue) {
    try {
        $pnpmStore = pnpm config get store-dir 2>$null
        if ($pnpmStore -like "*C:\pnpm-store*") {
            Write-ColorOutput "   ✅ PNPM store configured: $pnpmStore" $SuccessColor
        } else {
            Write-ColorOutput "   ⚠️  PNPM store not optimized" $WarningColor
            Write-ColorOutput "      Run: pnpm config set store-dir C:\pnpm-store" $WarningColor
        }
    } catch {
        Write-ColorOutput "   ⚠️  Could not check PNPM configuration" $WarningColor
    }
} else {
    Write-ColorOutput "   ℹ️  PNPM not installed, skipping store check" $InfoColor
}

# Summary
Write-ColorOutput ""
if ($allChecksPassed) {
    Write-ColorOutput "🎉 All critical checks passed! Windows path-length hotfix is working." $SuccessColor
} else {
    Write-ColorOutput "⚠️  Some checks failed. Review the warnings above." $WarningColor
}

Write-ColorOutput ""
Write-ColorOutput "📋 Next steps:" $InfoColor
Write-ColorOutput "  - Run: .\tools\windows_dev_shell.ps1 (for daily development)" $InfoColor
Write-ColorOutput "  - Test: python -m pytest -m 'phase6_perf or phase8_e2e' -q" $InfoColor
Write-ColorOutput "  - Cleanup: .\tools\windows_cleanup.ps1 (when done)" $InfoColor

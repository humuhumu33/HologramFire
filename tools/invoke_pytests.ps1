#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Windows-optimized pytest wrapper for Hologram pipeline.
    
.DESCRIPTION
    Ensures pytest runs with short paths and proper environment variables
    to avoid Windows path-length issues. This is the recommended way to
    run tests on Windows development machines.
    
.PARAMETER Mark
    Pytest marker to run (default: 'phase6_perf or phase8_e2e')
    
.PARAMETER ExtraArgs
    Additional arguments to pass to pytest
    
.EXAMPLE
    .\tools\invoke_pytests.ps1
    # Run default tests (phase6_perf or phase8_e2e)
    
.EXAMPLE
    .\tools\invoke_pytests.ps1 -Mark "phase1_core"
    # Run specific test phase
    
.EXAMPLE
    .\tools\invoke_pytests.ps1 -ExtraArgs "-v --tb=short"
    # Run with verbose output and short traceback
#>

param(
    [string]$Mark = 'phase6_perf or phase8_e2e',
    [string]$ExtraArgs = ''
)

# Colors for output
$InfoColor = "Cyan"
$SuccessColor = "Green"
$ErrorColor = "Red"

function Write-ColorOutput {
    param([string]$Message, [string]$Color = "White")
    Write-Host $Message -ForegroundColor $Color
}

Write-ColorOutput "🧪 Running Hologram tests with Windows path optimization..." $InfoColor

# Ensure short temp directories exist
Write-ColorOutput "   Ensuring temp directories..." $InfoColor
New-Item -ItemType Directory -Force C:\t\pt, C:\t\pc | Out-Null

# Set pytest environment variables for short paths
Write-ColorOutput "   Setting pytest environment..." $InfoColor
$env:PYTEST_ADDOPTS = '--basetemp=C:\t\pt -o cache_dir=C:\t\pc'

# Set short temp environment variables
$env:TMP = 'C:\t\tooltmp'
$env:TEMP = 'C:\t\tooltmp'
New-Item -ItemType Directory -Force C:\t\tooltmp | Out-Null

# Build pytest command
$pytestCmd = "python -m pytest -m `"$Mark`" -q"
if ($ExtraArgs) {
    $pytestCmd += " $ExtraArgs"
}

Write-ColorOutput "   Command: $pytestCmd" $InfoColor
Write-ColorOutput "   Temp dir: C:\t\pt" $InfoColor
Write-ColorOutput "   Cache dir: C:\t\pc" $InfoColor
Write-ColorOutput ""

# Run pytest
try {
    Invoke-Expression $pytestCmd
    $exitCode = $LASTEXITCODE
    
    if ($exitCode -eq 0) {
        Write-ColorOutput "`n✅ Tests completed successfully!" $SuccessColor
    } else {
        Write-ColorOutput "`n❌ Tests failed with exit code $exitCode" $ErrorColor
    }
    
    exit $exitCode
} catch {
    Write-ColorOutput "`n❌ Failed to run pytest: $($_.Exception.Message)" $ErrorColor
    exit 1
}

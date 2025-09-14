# Windows Development Setup

This guide helps Windows developers set up the Hologram pipeline without running into path-length issues that can break pytest and Node.js tools.

## The Problem

Windows has a 260-character path limit that can cause issues with:
- Deeply nested project structures
- Long temporary file paths
- Node.js module resolution
- Pytest test execution

## The Solution

Our Windows hotfix kit provides:
- **Short drive mapping** (repo → `X:\`)
- **Optimized temp directories** (`C:\t\pt`, `C:\t\pc`)
- **PNPM store optimization** (`C:\pnpm-store`)
- **Environment variable configuration**

## Quick Start

### Option 1: One-Time Setup (Recommended)

```powershell
# Run as Administrator (one-time only)
.\tools\windows_path_hotfix.ps1

# Daily development (run as user)
.\tools\windows_dev_shell.ps1
```

### Option 2: Make It Stick (PowerShell Profile)

```powershell
# Add to your PowerShell profile (automatic setup)
.\tools\windows_profile_setup.ps1

# Restart PowerShell - optimizations apply automatically
```

### Option 3: Manual Setup

```powershell
# Map repo to X: drive
subst X: (Resolve-Path .)
Set-Location X:\

# Set pytest environment
$env:PYTEST_ADDOPTS = '--basetemp=C:\t\pt -o cache_dir=C:\t\pc'

# Create temp directories
New-Item -ItemType Directory -Force C:\t\pt,C:\t\pc | Out-Null

# Configure PNPM
pnpm config set store-dir C:\pnpm-store
```

## Verification

Run the sanity check to verify everything is working:

```powershell
.\tools\windows_sanity_check.ps1
```

This will test:
- ✅ Windows long path support
- ✅ Git long paths configuration  
- ✅ X: drive mapping
- ✅ Pytest environment variables
- ✅ Short temp directories
- ✅ Path length capability (>260 chars)
- ✅ PNPM store configuration

## Daily Usage

Once set up, your daily workflow is:

```powershell
# Option 1: Start dev shell (if not using profile setup)
.\tools\windows_dev_shell.ps1

# Option 2: Use pytest wrapper (recommended)
.\tools\invoke_pytests.ps1

# Option 3: Dev shell with banner (new window)
.\tools\windows_dev_banner.ps1

# Run the pipeline
python -m pytest -m "phase6_perf or phase8_e2e" -q
python scripts/aggregate_reports.py
python scripts/check_perf_budget.py
```

## Cleanup

When you're done developing:

```powershell
# Remove all hotfix changes
.\tools\windows_cleanup.ps1

# Or remove from PowerShell profile
.\tools\windows_profile_setup.ps1 -Remove
```

## Troubleshooting

### Common Issues

**"Path too long" errors:**
- Verify `subst X:` is active
- Check `$env:PYTEST_ADDOPTS` shows short temp paths
- Run sanity check: `.\tools\windows_sanity_check.ps1`

**Corporate/managed machines:**
- Use only user-level changes (skip admin parts)
- Run: `.\tools\windows_path_hotfix.ps1 -UserOnly`

**Other tools ignoring pytest temp settings:**
```powershell
$env:TMP='C:\t\tmp'; $env:TEMP='C:\t\tmp'
# Run your command
```

**Deep temp paths from other tools:**
- Set short TMP for specific commands
- Use the dev shell script for consistent environment

### Manual Verification

```powershell
# Check drive mappings
subst

# Check environment variables
$env:PYTEST_ADDOPTS

# Test path length capability
$deep = "X:\a\" + ("verylong\" * 40)
New-Item -ItemType Directory $deep | Out-Null; Test-Path $deep
```

## Scripts Reference

| Script | Purpose | Admin Required |
|--------|---------|----------------|
| `windows_path_hotfix.ps1` | One-time setup | Yes (for OS changes) |
| `windows_dev_shell.ps1` | Daily development | No |
| `windows_dev_banner.ps1` | Dev shell with banner | No |
| `invoke_pytests.ps1` | Pytest wrapper | No |
| `windows_profile_setup.ps1` | Make it stick | No |
| `windows_sanity_check.ps1` | Verify setup | No |
| `windows_cleanup.ps1` | Remove changes | No |

## Advanced Configuration

### Custom Temp Directories

```powershell
# Use different temp directories
$env:PYTEST_ADDOPTS = '--basetemp=D:\temp\pytest -o cache_dir=D:\temp\cache'
```

### Multiple Repos

```powershell
# Map different repos to different drives
subst Y: C:\path\to\other\repo
subst Z: C:\path\to\another\repo
```

### CI/CD Integration

The hotfix kit is designed to be **CI-agnostic**:
- No changes needed for GitHub Actions
- No changes needed for other CI systems
- Only affects local Windows development

## Why This Works

1. **Windows MAX_PATH (260 chars)** still bites some tools
2. **Win32 long paths** help modern tools that opt-in
3. **Short path surface** reduces absolute path depth
4. **PNPM symlinks** already help with module resolution
5. **Environment variables** ensure consistent behavior

## Support

If you encounter issues:
1. Run `.\tools\windows_sanity_check.ps1`
2. Check the troubleshooting section above
3. Verify your PowerShell execution policy: `Get-ExecutionPolicy`
4. Try running with: `powershell -ExecutionPolicy Bypass -File script.ps1`

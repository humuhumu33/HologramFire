@echo off
REM IPFS Startup Batch Wrapper
REM Automatically handles lock issues and starts IPFS

if "%1"=="--force" (
    powershell.exe -ExecutionPolicy Bypass -File "%~dp0startup-ipfs.ps1" -Force
) else if "%1"=="--quiet" (
    powershell.exe -ExecutionPolicy Bypass -File "%~dp0startup-ipfs.ps1" -Quiet
) else (
    powershell.exe -ExecutionPolicy Bypass -File "%~dp0startup-ipfs.ps1"
)

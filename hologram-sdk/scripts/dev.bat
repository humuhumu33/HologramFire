@echo off
setlocal enabledelayedexpansion

REM Hologram SDK Development Helper (Windows)
REM Quick daemon startup with logging

set SCRIPT_DIR=%~dp0
set ENGINE_DIR=%SCRIPT_DIR%..\engine
set SOCKET_PATH=\\.\pipe\hologramd
set LOG_FILE=%TEMP%\hologramd.log

echo [%TIME%] Hologram SDK Development Mode
echo [%TIME%] =============================

REM Build the daemon
echo [%TIME%] Building hologramd...
cd /d "%ENGINE_DIR%"
go build -o hologramd.exe ./cmd/hologramd
if %errorlevel% neq 0 (
    echo [%TIME%] Failed to build hologramd
    exit /b 1
)
echo [%TIME%] Built hologramd successfully

REM Set environment variables from command line or defaults
if "%HOLOGRAM_VERBOSE%"=="" set HOLOGRAM_VERBOSE=
if "%HOLOGRAM_ENFORCE%"=="" set HOLOGRAM_ENFORCE=

echo [%TIME%] Starting hologramd...
echo [%TIME%] Environment:
echo [%TIME%]   HOLOGRAM_VERBOSE=%HOLOGRAM_VERBOSE%
echo [%TIME%]   HOLOGRAM_ENFORCE=%HOLOGRAM_ENFORCE%
echo [%TIME%]   Socket: %SOCKET_PATH%
echo [%TIME%]   Logs: %LOG_FILE%
echo [%TIME%] 
echo [%TIME%] Press Ctrl+C to stop
echo [%TIME%] 

REM Start daemon with live output
hologramd.exe --host=tcp --port=2375

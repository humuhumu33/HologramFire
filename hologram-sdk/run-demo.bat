@echo off
REM Hologram SDK Demo Runner for Windows
REM This script builds and runs hologramd for the demo

echo 🚀 Hologram SDK Demo Setup
echo ==========================
echo.

REM Check if Go is installed
go version >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ Go is not installed. Please install Go 1.21 or later.
    pause
    exit /b 1
)

echo ✅ Go is installed
go version
echo.

REM Build hologramd
echo 🔨 Building hologramd...
cd engine
go build -o hologramd.exe cmd/hologramd/main.go
if %errorlevel% neq 0 (
    echo ❌ Failed to build hologramd
    pause
    exit /b 1
)
echo ✅ hologramd built successfully
echo.

REM Start hologramd
echo 🚀 Starting hologramd...
echo    Socket: /var/run/hologramd.sock
echo    Mode: Docker compatibility
echo.

REM Note: On Windows, we'll use TCP mode instead of UNIX socket
echo 📡 Note: On Windows, using TCP mode instead of UNIX socket
echo    Port: 2375
echo.

REM Run hologramd
start /B hologramd.exe --host=0.0.0.0 --port=2375

REM Wait for hologramd to start
echo ⏳ Waiting for hologramd to start...
timeout /t 3 /nobreak >nul

REM Test connectivity
curl -s http://localhost:2375/_ping >nul 2>&1
if %errorlevel% neq 0 (
    echo ❌ hologramd failed to start
    pause
    exit /b 1
)

echo ✅ hologramd is running and responding
echo.
echo 🎯 Hologram SDK is ready!
echo.
echo Next steps:
echo 1. Set DOCKER_HOST: set DOCKER_HOST=tcp://localhost:2375
echo 2. Test: docker version
echo 3. Run examples: bash examples/run-all-examples.sh
echo.
echo Press any key to stop hologramd and exit
pause >nul

REM Stop hologramd
taskkill /F /IM hologramd.exe >nul 2>&1
echo ✅ hologramd stopped

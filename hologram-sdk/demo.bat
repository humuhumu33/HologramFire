@echo off
setlocal enabledelayedexpansion

REM Hologram SDK Demo - The "Cursor Aha" Moment (Windows)
REM Shows the progression from "It's just Docker" to "Oh wow" to "Never going back"

set SCRIPT_DIR=%~dp0
set ENGINE_DIR=%SCRIPT_DIR%engine
set SOCKET_PATH=\\.\pipe\hologramd
set LOG_FILE=%TEMP%\hologramd-demo.log

echo [%TIME%] Hologram SDK Demo - The Journey
echo ==================================
echo.

REM Build daemon
echo [%TIME%] Building hologramd...
cd /d "%ENGINE_DIR%"
go build -o hologramd.exe ./cmd/hologramd
if %errorlevel% neq 0 (
    echo [%TIME%] Build failed
    exit /b 1
)
echo [%TIME%] Built successfully

REM Start daemon in background
echo [%TIME%] Starting hologramd...
start /b hologramd.exe --host=tcp --port=2375 > "%LOG_FILE%" 2>&1
set DAEMON_PID=%!

REM Wait for daemon to start
timeout /t 3 /nobreak >nul

echo.
echo [%TIME%] Phase 1: 'It's just Docker'
echo [%TIME%] -------------------------------
echo [%TIME%] Testing basic Docker compatibility...

REM Test ping
curl -s http://localhost:2375/_ping >nul
if %errorlevel% equ 0 (
    echo [%TIME%] Ping works - it's just Docker!
) else (
    echo [%TIME%] Ping failed
    exit /b 1
)

REM Test version
for /f "tokens=*" %%i in ('curl -s http://localhost:2375/version ^| jq -r ".Version // \"unknown\""') do set VERSION=%%i
echo [%TIME%] Version: %VERSION% - standard Docker API

REM Test images list
for /f "tokens=*" %%i in ('curl -s http://localhost:2375/images/json ^| jq "length"') do set IMAGES=%%i
echo [%TIME%] Images endpoint works - found %IMAGES% images

echo.
echo [%TIME%] Phase 2: 'Oh wow' - The Magic Revealed
echo [%TIME%] ----------------------------------------
echo [%TIME%] Enabling verbose mode to see the magic...

REM Start daemon in verbose mode
taskkill /PID %DAEMON_PID% /F >nul 2>&1
timeout /t 1 /nobreak >nul
set HOLOGRAM_VERBOSE=1
start /b hologramd.exe --host=tcp --port=2375 > "%LOG_FILE%" 2>&1
set DAEMON_PID=%!
timeout /t 3 /nobreak >nul

echo [%TIME%] Checking images with verbose mode...
curl -s http://localhost:2375/images/json | jq ".[0].XHologram" >nul 2>&1
if %errorlevel% equ 0 (
    echo [%TIME%] XHologram fields appear! UOR-IDs and witness status revealed!
    curl -s http://localhost:2375/images/json | jq ".[0].XHologram"
) else (
    echo [%TIME%] No XHologram fields yet - need to pull an image
)

echo [%TIME%] Pulling test image with verbose progress...
curl -s "http://localhost:2375/images/create?fromImage=holo-test-ok&tag=latest" | findstr "XHologram" >nul
if %errorlevel% equ 0 (
    echo [%TIME%] XHologram progress messages in the stream!
    curl -s "http://localhost:2375/images/create?fromImage=holo-test-ok&tag=latest" | findstr "XHologram" | head -1
) else (
    echo [%TIME%] Progress stream working, but no XHologram messages visible
)

echo.
echo [%TIME%] Phase 3: 'Never going back' - Security Enforcement
echo [%TIME%] --------------------------------------------------
echo [%TIME%] Enabling enforce mode for security...

REM Start daemon in enforce mode
taskkill /PID %DAEMON_PID% /F >nul 2>&1
timeout /t 1 /nobreak >nul
set HOLOGRAM_VERBOSE=
set HOLOGRAM_ENFORCE=1
start /b hologramd.exe --host=tcp --port=2375 > "%LOG_FILE%" 2>&1
set DAEMON_PID=%!
timeout /t 3 /nobreak >nul

echo [%TIME%] Attempting to pull image with bad witness...
curl -s -w "%%{http_code}" "http://localhost:2375/images/create?fromImage=holo-test-bad&tag=latest" > "%TEMP%\enforce_output.txt"
for /f "tokens=*" %%i in ('type "%TEMP%\enforce_output.txt"') do set ENFORCE_OUTPUT=%%i
set HTTP_CODE=%ENFORCE_OUTPUT:~-4%
set RESPONSE_BODY=%ENFORCE_OUTPUT:~0,-4%

if "%HTTP_CODE%"=="400" (
    echo [%TIME%] Enforce mode blocked bad witness! Security working!
    echo [%TIME%] HTTP %HTTP_CODE%: %RESPONSE_BODY%
) else (
    echo [%TIME%] Expected 400 error, got HTTP %HTTP_CODE%
)

echo [%TIME%] Attempting to pull image with good witness...
curl -s -w "%%{http_code}" "http://localhost:2375/images/create?fromImage=holo-test-ok&tag=latest" > "%TEMP%\good_output.txt"
for /f "tokens=*" %%i in ('type "%TEMP%\good_output.txt"') do set GOOD_OUTPUT=%%i
set GOOD_HTTP_CODE=%GOOD_OUTPUT:~-4%

if "%GOOD_HTTP_CODE%"=="200" (
    echo [%TIME%] Good witness allowed through - selective enforcement working!
) else (
    echo [%TIME%] Expected 200 success, got HTTP %GOOD_HTTP_CODE%
)

echo.
echo [%TIME%] Demo Complete!
echo [%TIME%] ================
echo.
echo [%TIME%] You've seen the journey:
echo [%TIME%]   1. It's just Docker - Perfect compatibility
echo [%TIME%]   2. Oh wow - Hologram magic revealed
echo [%TIME%]   3. Never going back - Security enforcement
echo.
echo [%TIME%] The Hologram SDK: Docker-compatible with superpowers!
echo.
echo [%TIME%] Check %LOG_FILE% for detailed daemon output

REM Cleanup
taskkill /PID %DAEMON_PID% /F >nul 2>&1
del "%TEMP%\enforce_output.txt" >nul 2>&1
del "%TEMP%\good_output.txt" >nul 2>&1

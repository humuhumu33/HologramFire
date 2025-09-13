@echo off
setlocal enabledelayedexpansion

REM Hologram SDK Test Runner (Windows)
REM Supports 3 modes: compat, verbose, enforce

set MODE=%1
if "%MODE%"=="" set MODE=compat

set SCRIPT_DIR=%~dp0
set ENGINE_DIR=%SCRIPT_DIR%engine
set TESTS_DIR=%SCRIPT_DIR%..\tests\go
set SOCKET_PATH=\\.\pipe\hologramd
set PID_FILE=%SCRIPT_DIR%.pid
set LOG_FILE=%TEMP%\hologramd.log

echo [%TIME%] Starting Hologram SDK tests in %MODE% mode...

:cleanup
if exist "%PID_FILE%" (
    set /p PID=<"%PID_FILE%"
    taskkill /PID !PID! /F >nul 2>&1
    del "%PID_FILE%" >nul 2>&1
)
goto :eof

:build_daemon
echo [%TIME%] Building hologramd...
cd /d "%ENGINE_DIR%"
go build -o hologramd.exe ./cmd/hologramd
if %errorlevel% neq 0 (
    echo [%TIME%] Failed to build hologramd
    exit /b 1
)
echo [%TIME%] Built hologramd successfully
goto :eof

:start_daemon
set VERBOSE=%1
set ENFORCE=%2

echo [%TIME%] Starting hologramd in %MODE% mode...

REM Set environment variables
if "%VERBOSE%"=="1" set HOLOGRAM_VERBOSE=1
if "%ENFORCE%"=="1" set HOLOGRAM_ENFORCE=1

REM Start daemon in background
cd /d "%ENGINE_DIR%"
start /b hologramd.exe --host=tcp --port=2375 > "%LOG_FILE%" 2>&1
echo %! > "%PID_FILE%"

REM Wait for daemon to start
set /a attempts=0
:wait_loop
if %attempts% geq 30 (
    echo [%TIME%] Failed to start hologramd (timeout)
    type "%LOG_FILE%"
    exit /b 1
)
timeout /t 1 /nobreak >nul
set /a attempts+=1
netstat -an | findstr ":2375" >nul
if %errorlevel% neq 0 goto wait_loop

echo [%TIME%] Hologramd started
goto :eof

:run_tests
set TEST_FILTER=%1
set ENV_VARS=%2

echo [%TIME%] Running tests...

REM Set environment for tests
set DOCKER_HOST=tcp://localhost:2375
if not "%ENV_VARS%"=="" %ENV_VARS%

cd /d "%TESTS_DIR%"

set TEST_CMD=go test -count=1
if not "%TEST_FILTER%"=="" set TEST_CMD=%TEST_CMD% -run %TEST_FILTER%

%TEST_CMD%
if %errorlevel% neq 0 (
    echo [%TIME%] Tests failed
    exit /b 1
)

echo [%TIME%] All tests passed
goto :eof

REM Main execution
if "%MODE%"=="compat" (
    call :build_daemon
    call :start_daemon "" ""
    call :run_tests "" ""
) else if "%MODE%"=="verbose" (
    call :build_daemon
    call :start_daemon "1" ""
    call :run_tests "Verbose" "set HOLOGRAM_VERBOSE=1"
) else if "%MODE%"=="enforce" (
    call :build_daemon
    call :start_daemon "" "1"
    call :run_tests "Enforce" "set HOLOGRAM_ENFORCE=1"
) else (
    echo [%TIME%] Unknown mode: %MODE%
    echo Usage: %0 [compat^|verbose^|enforce]
    exit /b 1
)

call :cleanup
echo [%TIME%] Test run completed successfully in %MODE% mode

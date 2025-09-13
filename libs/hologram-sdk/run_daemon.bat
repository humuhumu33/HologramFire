@echo off

REM Run hologramd daemon for testing

echo Starting Hologram daemon...

REM Build the daemon
cd engine
go build -o hologramd.exe ./cmd/hologramd

if %errorlevel% neq 0 (
    echo Failed to build hologramd
    exit /b 1
)

echo Built hologramd successfully

REM Run the daemon with TCP (Windows doesn't support UNIX sockets easily)
echo Starting daemon on TCP...
hologramd.exe --host=0.0.0.0 --port=2375 --hologram-enabled --hologram-uor-id --hologram-witness

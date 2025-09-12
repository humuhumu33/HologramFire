@echo off
REM Firebase Studio PWA Launcher
REM This script launches the Firebase Studio PWA directly from GitHub repo

echo 🚀 Starting Firebase Studio PWA...
echo.

REM Check if we're in the right directory
if not exist "firebase-studio-frontend" (
    echo ❌ Error: firebase-studio-frontend directory not found.
    echo Please run this script from the HologramFire root directory.
    pause
    exit /b 1
)

REM Navigate to frontend directory
cd firebase-studio-frontend

REM Check if node_modules exists
if not exist "node_modules" (
    echo 📦 Installing dependencies...
    call npm install
    if errorlevel 1 (
        echo ❌ Error: Failed to install dependencies
        pause
        exit /b 1
    )
)

REM Build the PWA
echo 🏗️  Building Firebase Studio PWA...
call npm run build
if errorlevel 1 (
    echo ❌ Error: Build failed
    pause
    exit /b 1
)

REM Start the preview server
echo 🌐 Starting PWA server...
echo.
echo ✅ Firebase Studio PWA is now running!
echo 🔗 Open your browser and go to: http://localhost:3000
echo.
echo 📱 PWA Features:
echo    • Installable on mobile and desktop
echo    • Offline functionality
echo    • Smooth animations and transitions
echo    • Responsive design
echo.
echo ⚡ Performance:
echo    • Optimized bundle with code splitting
echo    • Service worker caching
echo    • Modern UI with Revolut-inspired design
echo.
echo Press Ctrl+C to stop the server
echo.

call npm run preview

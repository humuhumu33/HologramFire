@echo off
REM Firebase Studio Deployment Script for Windows
REM This script builds and deploys the Firebase Studio frontend to GitHub Pages

echo 🚀 Starting Firebase Studio deployment...

REM Check if we're in the right directory
if not exist "package.json" (
    echo ❌ Error: package.json not found. Please run this script from the firebase-studio-frontend directory.
    pause
    exit /b 1
)

REM Install dependencies
echo 📦 Installing dependencies...
call npm ci
if errorlevel 1 (
    echo ❌ Error: Failed to install dependencies
    pause
    exit /b 1
)

REM Run linting
echo 🔍 Running linter...
call npm run lint
if errorlevel 1 (
    echo ⚠️  Warning: Linting issues found, but continuing...
)

REM Run tests
echo 🧪 Running tests...
call npm run test
if errorlevel 1 (
    echo ⚠️  Warning: Some tests failed, but continuing...
)

REM Build the application
echo 🏗️  Building application...
call npm run build
if errorlevel 1 (
    echo ❌ Error: Build failed
    pause
    exit /b 1
)

REM Check if build was successful
if not exist "dist" (
    echo ❌ Error: Build failed. dist directory not found.
    pause
    exit /b 1
)

echo ✅ Build completed successfully!

REM Deploy to GitHub Pages
echo 🌐 Deploying to GitHub Pages...
call npm run deploy:gh-pages
if errorlevel 1 (
    echo ❌ Error: Deployment failed
    pause
    exit /b 1
)

echo 🎉 Deployment completed successfully!
echo 🔗 Your app is now available at: https://your-username.github.io/HologramFire/firebase-studio-frontend/
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
pause
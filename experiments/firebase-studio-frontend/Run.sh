#!/bin/bash

# Firebase Studio PWA Launcher
# This script launches the Firebase Studio PWA directly from GitHub repo

echo "🚀 Starting Firebase Studio PWA..."
echo

# Check if we're in the right directory
if [ ! -f "package.json" ]; then
    echo "❌ Error: package.json not found."
    echo "Please run this script from the firebase-studio-frontend directory."
    exit 1
fi

# Check if node_modules exists
if [ ! -d "node_modules" ]; then
    echo "📦 Installing dependencies..."
    npm install
    if [ $? -ne 0 ]; then
        echo "❌ Error: Failed to install dependencies"
        exit 1
    fi
fi

# Build the PWA
echo "🏗️  Building Firebase Studio PWA..."
npm run build
if [ $? -ne 0 ]; then
    echo "❌ Error: Build failed"
    exit 1
fi

# Start the preview server
echo "🌐 Starting PWA server..."
echo
echo "✅ Firebase Studio PWA is now running!"
echo "🔗 Open your browser and go to: http://localhost:3000"
echo
echo "📱 PWA Features:"
echo "   • Installable on mobile and desktop"
echo "   • Offline functionality"
echo "   • Smooth animations and transitions"
echo "   • Responsive design"
echo
echo "⚡ Performance:"
echo "   • Optimized bundle with code splitting"
echo "   • Service worker caching"
echo "   • Modern UI with Revolut-inspired design"
echo
echo "Press Ctrl+C to stop the server"
echo

npm run preview

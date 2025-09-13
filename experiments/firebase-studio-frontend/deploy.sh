#!/bin/bash

# Firebase Studio Deployment Script
# This script builds and deploys the Firebase Studio frontend to GitHub Pages

set -e

echo "🚀 Starting Firebase Studio deployment..."

# Check if we're in the right directory
if [ ! -f "package.json" ]; then
    echo "❌ Error: package.json not found. Please run this script from the firebase-studio-frontend directory."
    exit 1
fi

# Install dependencies
echo "📦 Installing dependencies..."
npm ci

# Run linting
echo "🔍 Running linter..."
npm run lint

# Run tests
echo "🧪 Running tests..."
npm run test

# Build the application
echo "🏗️  Building application..."
npm run build

# Check if build was successful
if [ ! -d "dist" ]; then
    echo "❌ Error: Build failed. dist directory not found."
    exit 1
fi

echo "✅ Build completed successfully!"

# Deploy to GitHub Pages
echo "🌐 Deploying to GitHub Pages..."
npm run deploy:gh-pages

echo "🎉 Deployment completed successfully!"
echo "🔗 Your app is now available at: https://$(git config user.name).github.io/HologramFire/firebase-studio-frontend/"
echo ""
echo "📱 PWA Features:"
echo "   • Installable on mobile and desktop"
echo "   • Offline functionality"
echo "   • Smooth animations and transitions"
echo "   • Responsive design"
echo ""
echo "⚡ Performance:"
echo "   • Optimized bundle with code splitting"
echo "   • Service worker caching"
echo "   • Modern UI with Revolut-inspired design"
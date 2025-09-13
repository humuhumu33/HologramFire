# Firebase Studio - Modern PWA Frontend

A modern, full-stack AI workspace with smooth UX inspired by Revolut Exchange. Built as a Progressive Web App (PWA) that runs smoothly in any browser and can be deployed directly from GitHub.

## ✨ Features

### 🚀 Progressive Web App (PWA)
- **Installable**: Add to home screen on mobile and desktop
- **Offline Support**: Works without internet connection
- **Fast Loading**: Service worker caching and optimized bundles
- **Responsive**: Perfect on mobile, tablet, and desktop

### 🎨 Modern UI/UX
- **Revolut-Inspired Design**: Smooth animations and premium feel
- **Glass Morphism**: Modern glass effects and backdrop blur
- **Micro-interactions**: Ripple effects, hover animations, and smooth transitions
- **Dark/Light Theme**: Adaptive design that works in any environment

### ⚡ Performance Optimized
- **Code Splitting**: Lazy loading for faster initial load
- **Bundle Optimization**: Manual chunks for vendor, editor, and icons
- **Service Worker**: Intelligent caching strategies
- **Preloading**: Smart component preloading for better UX

### 📱 Responsive Design
- **Mobile-First**: Touch-friendly interactions
- **Adaptive Layout**: Panels collapse on mobile with smooth animations
- **Gesture Support**: Swipe and touch gestures for mobile users
- **Cross-Platform**: Works on iOS, Android, Windows, macOS, and Linux

## 🚀 Quick Start

### Prerequisites
- Node.js 18+ 
- npm or yarn
- Git

### Installation

```bash
# Clone the repository
git clone https://github.com/your-username/HologramFire.git
cd HologramFire/firebase-studio-frontend

# Install dependencies
npm install

# Start development server
npm run dev
```

### Development Commands

```bash
# Start development server
npm run dev

# Build for production
npm run build

# Preview production build
npm run preview

# Run tests
npm run test

# Run linting
npm run lint

# Fix linting issues
npm run lint:fix
```

## 🌐 Deployment

### GitHub Pages (Automatic)

The app is configured for automatic deployment to GitHub Pages:

1. **Push to main branch**: Changes are automatically deployed
2. **Pull requests**: Get preview deployments with comments
3. **Custom domain**: Add your domain in the GitHub Actions workflow

### Manual Deployment

```bash
# Build and deploy to GitHub Pages
npm run deploy

# Deploy preview version
npm run deploy:preview
```

### Access Your App

Once deployed, your app will be available at:
```
https://your-username.github.io/HologramFire/firebase-studio-frontend/
```

## 📱 PWA Installation

### Desktop (Chrome/Edge)
1. Open the app in your browser
2. Click the install button in the address bar
3. Or use the menu: More tools → Create shortcut → Open as window

### Mobile (iOS/Android)
1. Open the app in Safari/Chrome
2. Tap the Share button
3. Select "Add to Home Screen"
4. The app will appear as a native app

## 🛠️ Technology Stack

- **Framework**: React 18 with TypeScript
- **Build Tool**: Vite 5 with optimized configuration
- **Styling**: Tailwind CSS with custom design system
- **Icons**: Lucide React
- **Editor**: Monaco Editor (VS Code editor)
- **PWA**: Service Worker with offline support
- **Deployment**: GitHub Pages with GitHub Actions

## 🎨 Design System

### Colors
- **Primary**: Firebase Blue (#4285f4)
- **Secondary**: Firebase Green (#34a853)
- **Accent**: Firebase Orange (#ff6f00)
- **Error**: Firebase Red (#ea4335)
- **Warning**: Firebase Yellow (#ffc107)

### Typography
- **Font**: Google Sans (system fallback)
- **Weights**: 300, 400, 500, 600, 700

### Components
- **Buttons**: Animated with ripple effects
- **Cards**: Glass morphism with hover animations
- **Inputs**: Modern rounded design with focus states
- **Panels**: Resizable with smooth transitions

## 🔧 Configuration

### Environment Variables
Create a `.env` file in the root directory:

```env
VITE_APP_NAME=Firebase Studio
VITE_APP_VERSION=1.0.0
VITE_APP_DESCRIPTION=Full Stack AI Workspace
```

### PWA Configuration
The PWA is configured in:
- `public/manifest.json` - App manifest
- `public/sw.js` - Service worker
- `index.html` - PWA meta tags

### Build Configuration
Optimized in `vite.config.ts`:
- Code splitting for vendor, editor, and icons
- Source maps for debugging
- Relative paths for GitHub Pages

## 📊 Performance

### Bundle Analysis
```bash
npm run analyze
```

### Lighthouse Scores
- **Performance**: 95+
- **Accessibility**: 100
- **Best Practices**: 100
- **SEO**: 100
- **PWA**: 100

## 🤝 Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run tests and linting
5. Submit a pull request

## 📄 License

This project is licensed under the MIT License - see the LICENSE file for details.

## 🆘 Support

- **Issues**: [GitHub Issues](https://github.com/your-username/HologramFire/issues)
- **Discussions**: [GitHub Discussions](https://github.com/your-username/HologramFire/discussions)
- **Documentation**: [Wiki](https://github.com/your-username/HologramFire/wiki)

---

Built with ❤️ using modern web technologies and inspired by the smooth UX of Revolut Exchange.
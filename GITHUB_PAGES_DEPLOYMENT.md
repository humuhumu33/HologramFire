# GitHub Pages Deployment Guide

This guide explains how to deploy your PWA to GitHub Pages using GitHub Actions.

## 🚀 Quick Setup

### 1. Enable GitHub Pages
1. Go to your repository on GitHub
2. Navigate to **Settings** → **Pages**
3. Under **Source**, select **"GitHub Actions"**
4. Save the settings

### 2. Push to Deploy
Simply push your changes to the `main` branch. The GitHub Actions workflow will automatically:
- Build your PWA
- Create a 404.html fallback for SPA routing
- Deploy to GitHub Pages

## 📁 Project Structure

Your PWA is located in the `firebase-studio-frontend/` directory and will be deployed to:
```
https://pavel.github.io/HologramFire/firebase-studio-frontend/
```

## ⚙️ Configuration Details

### Vite Configuration
- **Base path**: `/HologramFire/firebase-studio-frontend/`
- **Build output**: `dist/` directory
- **SPA fallback**: Automatically creates `404.html` from `index.html`

### PWA Manifest
- **Start URL**: `/HologramFire/firebase-studio-frontend/?source=pwa`
- **Scope**: `/HologramFire/firebase-studio-frontend/`
- **Icons**: All paths updated for GitHub Pages

### Service Worker
- **Registration scope**: `/HologramFire/firebase-studio-frontend/`
- **Cache paths**: Updated for GitHub Pages base path
- **Offline fallback**: Points to correct index.html location

## 🔧 Manual Deployment

If you need to deploy manually:

```bash
cd firebase-studio-frontend
npm run build
npm run deploy:gh-pages
```

## 🐛 Troubleshooting

### Common Issues

1. **404 errors on refresh**: Ensure `404.html` is created during build
2. **Service worker not registering**: Check the scope matches your base path
3. **Assets not loading**: Verify all paths use the correct base path
4. **PWA not installable**: Check manifest.json paths and scope

### Debug Steps

1. Check the GitHub Actions workflow logs
2. Verify the deployed files in the `gh-pages` branch
3. Test the PWA in Chrome DevTools → Application tab
4. Check the service worker registration in the Console

## 📱 PWA Features

Your deployed PWA includes:
- ✅ Offline functionality
- ✅ Install prompt
- ✅ Push notifications
- ✅ Background sync
- ✅ App shortcuts
- ✅ Responsive design

## 🔄 Custom Domain (Optional)

To use a custom domain:
1. Add a `CNAME` file to your repository root with your domain
2. Configure DNS settings to point to `pavel.github.io`
3. Enable HTTPS in GitHub Pages settings

## 📊 Performance

The deployment includes:
- Automatic asset optimization
- Code splitting
- Service worker caching
- Font preloading
- Critical resource preloading

## 🚨 Security

- HTTPS enabled by default
- Service worker scoped to your app
- No sensitive data in client-side code
- Secure headers via GitHub Pages

---

**Need help?** Check the GitHub Actions logs or open an issue in the repository.

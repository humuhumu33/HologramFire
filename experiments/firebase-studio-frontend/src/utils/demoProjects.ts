export const createDemoProject = () => {
  return {
    id: 'demo-project',
    name: 'Firebase Studio Demo',
    files: [
      {
        id: '1',
        name: 'index.html',
        content: `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Firebase Studio Demo</title>
    <link rel="stylesheet" href="styles.css">
</head>
<body>
    <div class="container">
        <header>
            <h1>Welcome to Firebase Studio</h1>
            <p>Build amazing apps with AI assistance</p>
        </header>
        
        <main>
            <div class="feature-grid">
                <div class="feature-card">
                    <h3>AI-Powered Coding</h3>
                    <p>Get help from Gemini AI for coding, debugging, and more.</p>
                </div>
                <div class="feature-card">
                    <h3>Live Preview</h3>
                    <p>See your changes in real-time across different devices.</p>
                </div>
                <div class="feature-card">
                    <h3>Full-Stack Development</h3>
                    <p>Build backends, frontends, and mobile apps in one place.</p>
                </div>
            </div>
        </main>
        
        <footer>
            <p>&copy; 2024 Firebase Studio. Built with ❤️</p>
        </footer>
    </div>
    
    <script src="script.js"></script>
</body>
</html>`,
        type: 'html' as const,
        path: '/index.html'
      },
      {
        id: '2',
        name: 'styles.css',
        content: `/* Firebase Studio Demo Styles */
* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

body {
    font-family: 'Google Sans', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
    line-height: 1.6;
    color: #202124;
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    min-height: 100vh;
}

.container {
    max-width: 1200px;
    margin: 0 auto;
    padding: 2rem;
}

header {
    text-align: center;
    margin-bottom: 3rem;
    color: white;
}

header h1 {
    font-size: 3rem;
    font-weight: 700;
    margin-bottom: 1rem;
    text-shadow: 0 2px 4px rgba(0,0,0,0.3);
}

header p {
    font-size: 1.2rem;
    opacity: 0.9;
}

.feature-grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
    gap: 2rem;
    margin-bottom: 3rem;
}

.feature-card {
    background: white;
    padding: 2rem;
    border-radius: 12px;
    box-shadow: 0 4px 6px rgba(0,0,0,0.1);
    transition: transform 0.3s ease, box-shadow 0.3s ease;
}

.feature-card:hover {
    transform: translateY(-4px);
    box-shadow: 0 8px 25px rgba(0,0,0,0.15);
}

.feature-card h3 {
    color: #4285f4;
    margin-bottom: 1rem;
    font-size: 1.5rem;
}

.feature-card p {
    color: #5f6368;
    line-height: 1.6;
}

footer {
    text-align: center;
    color: white;
    opacity: 0.8;
}

@media (max-width: 768px) {
    .container {
        padding: 1rem;
    }
    
    header h1 {
        font-size: 2rem;
    }
    
    .feature-grid {
        grid-template-columns: 1fr;
    }
}`,
        type: 'css' as const,
        path: '/styles.css'
      },
      {
        id: '3',
        name: 'script.js',
        content: `// Firebase Studio Demo JavaScript
console.log('🚀 Firebase Studio Demo loaded!');

// Initialize the demo
document.addEventListener('DOMContentLoaded', function() {
    console.log('📱 DOM loaded, initializing demo...');
    
    // Add interactive features
    initializeFeatureCards();
    addSmoothScrolling();
    setupAnimations();
});

function initializeFeatureCards() {
    const cards = document.querySelectorAll('.feature-card');
    
    cards.forEach((card, index) => {
        // Add staggered animation
        card.style.opacity = '0';
        card.style.transform = 'translateY(20px)';
        
        setTimeout(() => {
            card.style.transition = 'opacity 0.6s ease, transform 0.6s ease';
            card.style.opacity = '1';
            card.style.transform = 'translateY(0)';
        }, index * 200);
        
        // Add click interaction
        card.addEventListener('click', function() {
            this.style.transform = 'scale(0.98)';
            setTimeout(() => {
                this.style.transform = 'scale(1)';
            }, 150);
        });
    });
}

function addSmoothScrolling() {
    // Add smooth scrolling to any anchor links
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', function (e) {
            e.preventDefault();
            const target = document.querySelector(this.getAttribute('href'));
            if (target) {
                target.scrollIntoView({
                    behavior: 'smooth',
                    block: 'start'
                });
            }
        });
    });
}

function setupAnimations() {
    // Add parallax effect to header
    window.addEventListener('scroll', function() {
        const scrolled = window.pageYOffset;
        const header = document.querySelector('header');
        
        if (header) {
            header.style.transform = \`translateY(\${scrolled * 0.5}px)\`;
        }
    });
    
    // Add typing effect to title
    const title = document.querySelector('header h1');
    if (title) {
        const text = title.textContent;
        title.textContent = '';
        
        let i = 0;
        const typeWriter = () => {
            if (i < text.length) {
                title.textContent += text.charAt(i);
                i++;
                setTimeout(typeWriter, 100);
            }
        };
        
        setTimeout(typeWriter, 500);
    }
}

// Utility functions
function showNotification(message, type = 'info') {
    const notification = document.createElement('div');
    notification.className = \`notification notification-\${type}\`;
    notification.textContent = message;
    
    notification.style.cssText = \`
        position: fixed;
        top: 20px;
        right: 20px;
        padding: 1rem 2rem;
        background: \${type === 'success' ? '#34a853' : type === 'error' ? '#ea4335' : '#4285f4'};
        color: white;
        border-radius: 8px;
        box-shadow: 0 4px 6px rgba(0,0,0,0.1);
        z-index: 1000;
        animation: slideIn 0.3s ease;
    \`;
    
    document.body.appendChild(notification);
    
    setTimeout(() => {
        notification.style.animation = 'slideOut 0.3s ease';
        setTimeout(() => {
            document.body.removeChild(notification);
        }, 300);
    }, 3000);
}

// Add CSS animations
const style = document.createElement('style');
style.textContent = \`
    @keyframes slideIn {
        from { transform: translateX(100%); opacity: 0; }
        to { transform: translateX(0); opacity: 1; }
    }
    
    @keyframes slideOut {
        from { transform: translateX(0); opacity: 1; }
        to { transform: translateX(100%); opacity: 0; }
    }
\`;
document.head.appendChild(style);

// Export for potential use in other modules
window.FirebaseStudioDemo = {
    showNotification,
    initializeFeatureCards,
    addSmoothScrolling,
    setupAnimations
};`,
        type: 'javascript' as const,
        path: '/script.js'
      },
      {
        id: '4',
        name: 'package.json',
        content: `{
  "name": "firebase-studio-demo",
  "version": "1.0.0",
  "description": "A demo project showcasing Firebase Studio capabilities",
  "main": "script.js",
  "scripts": {
    "start": "python -m http.server 8000",
    "dev": "live-server --port=8000",
    "build": "echo 'No build step required for this demo'",
    "test": "echo 'No tests specified'"
  },
  "keywords": [
    "firebase",
    "studio",
    "demo",
    "web",
    "development"
  ],
  "author": "Firebase Studio Team",
  "license": "MIT",
  "devDependencies": {
    "live-server": "^1.2.2"
  },
  "dependencies": {},
  "repository": {
    "type": "git",
    "url": "https://github.com/firebase/studio-demo.git"
  },
  "bugs": {
    "url": "https://github.com/firebase/studio-demo/issues"
  },
  "homepage": "https://github.com/firebase/studio-demo#readme"
}`,
        type: 'json' as const,
        path: '/package.json'
      }
    ],
    createdAt: new Date(),
    updatedAt: new Date()
  }
}

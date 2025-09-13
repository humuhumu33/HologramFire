#!/usr/bin/env node

const http = require('http');
const fs = require('fs');
const path = require('path');
const url = require('url');

const PORT = process.env.PORT || 3000;
const DIST_DIR = path.join(__dirname, 'dist');

// MIME types for different file extensions
const mimeTypes = {
    '.html': 'text/html',
    '.js': 'text/javascript',
    '.css': 'text/css',
    '.json': 'application/json',
    '.png': 'image/png',
    '.jpg': 'image/jpg',
    '.gif': 'image/gif',
    '.svg': 'image/svg+xml',
    '.ico': 'image/x-icon',
    '.woff': 'font/woff',
    '.woff2': 'font/woff2',
    '.ttf': 'font/ttf',
    '.eot': 'application/vnd.ms-fontobject'
};

const server = http.createServer((req, res) => {
    const parsedUrl = url.parse(req.url);
    let pathname = parsedUrl.pathname;
    
    // Default to index.html for root path
    if (pathname === '/') {
        pathname = '/index.html';
    }
    
    const filePath = path.join(DIST_DIR, pathname);
    const ext = path.extname(filePath).toLowerCase();
    const mimeType = mimeTypes[ext] || 'application/octet-stream';
    
    // Check if file exists
    fs.access(filePath, fs.constants.F_OK, (err) => {
        if (err) {
            // File not found, serve index.html for SPA routing
            const indexPath = path.join(DIST_DIR, 'index.html');
            fs.readFile(indexPath, (err, data) => {
                if (err) {
                    res.writeHead(404, { 'Content-Type': 'text/plain' });
                    res.end('404 Not Found');
                    return;
                }
                res.writeHead(200, { 'Content-Type': 'text/html' });
                res.end(data);
            });
            return;
        }
        
        // Read and serve the file
        fs.readFile(filePath, (err, data) => {
            if (err) {
                res.writeHead(500, { 'Content-Type': 'text/plain' });
                res.end('500 Internal Server Error');
                return;
            }
            
            // Set appropriate headers
            const headers = {
                'Content-Type': mimeType,
                'Cache-Control': ext === '.html' ? 'no-cache' : 'public, max-age=31536000'
            };
            
            // Add PWA headers
            if (ext === '.html') {
                headers['X-Content-Type-Options'] = 'nosniff';
                headers['X-Frame-Options'] = 'DENY';
                headers['X-XSS-Protection'] = '1; mode=block';
            }
            
            res.writeHead(200, headers);
            res.end(data);
        });
    });
});

server.listen(PORT, () => {
    console.log('🚀 Firebase Studio PWA Server');
    console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
    console.log(`✅ Server running at: http://localhost:${PORT}`);
    console.log(`📱 PWA Features: Installable, Offline, Responsive`);
    console.log(`🎨 UI: Revolut-inspired modern design`);
    console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
    console.log('Press Ctrl+C to stop the server');
});

// Graceful shutdown
process.on('SIGINT', () => {
    console.log('\n👋 Shutting down Firebase Studio PWA server...');
    server.close(() => {
        console.log('✅ Server stopped');
        process.exit(0);
    });
});

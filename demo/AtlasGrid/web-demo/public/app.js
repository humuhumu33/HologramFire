/**
 * Atlas-12288 Interactive Demo Client
 * 
 * Real-time web interface for demonstrating Atlas functionality
 */

class AtlasDemoClient {
    constructor() {
        this.ws = null;
        this.isConnected = false;
        this.currentResults = null;
        this.gridCells = [];
        this.r96Classes = [];
        
        this.initializeElements();
        this.setupEventListeners();
        this.connectWebSocket();
        this.loadDemoData();
        this.loadGridStats();
    }

    initializeElements() {
        // Input elements
        this.dataNameInput = document.getElementById('dataName');
        this.dataContentInput = document.getElementById('dataContent');
        this.mimeTypeSelect = document.getElementById('mimeType');
        this.processBtn = document.getElementById('processBtn');
        this.verifyBtn = document.getElementById('verifyBtn');
        
        // Result elements
        this.resultsContainer = document.getElementById('results');
        this.gridContainer = document.getElementById('grid');
        this.r96Container = document.getElementById('r96Visualization');
        this.demoDataContainer = document.getElementById('demoDataSets');
        this.performanceContainer = document.getElementById('performanceMetrics');
        
        // Grid stats elements
        this.totalCoordsSpan = document.getElementById('totalCoords');
        this.pagesSpan = document.getElementById('pages');
        this.cyclesSpan = document.getElementById('cycles');
        this.r96ClassesSpan = document.getElementById('r96Classes');
        
        // Performance elements
        this.processingTimeSpan = document.getElementById('processingTime');
        this.dataSizeSpan = document.getElementById('dataSize');
        this.uniqueBytesSpan = document.getElementById('uniqueBytes');
        this.entropySpan = document.getElementById('entropy');
    }

    setupEventListeners() {
        this.processBtn.addEventListener('click', () => this.processData());
        this.verifyBtn.addEventListener('click', () => this.verifyDeterministic());
        
        // Auto-process on Enter key
        this.dataContentInput.addEventListener('keydown', (e) => {
            if (e.ctrlKey && e.key === 'Enter') {
                this.processData();
            }
        });
    }

    connectWebSocket() {
        const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
        const wsUrl = `${protocol}//${window.location.host}`;
        
        this.ws = new WebSocket(wsUrl);
        
        this.ws.onopen = () => {
            this.isConnected = true;
            console.log('Connected to Atlas demo server');
            this.updateConnectionStatus(true);
        };
        
        this.ws.onmessage = (event) => {
            const message = JSON.parse(event.data);
            this.handleWebSocketMessage(message);
        };
        
        this.ws.onclose = () => {
            this.isConnected = false;
            console.log('Disconnected from Atlas demo server');
            this.updateConnectionStatus(false);
            
            // Attempt to reconnect after 3 seconds
            setTimeout(() => this.connectWebSocket(), 3000);
        };
        
        this.ws.onerror = (error) => {
            console.error('WebSocket error:', error);
            this.updateConnectionStatus(false);
        };
    }

    handleWebSocketMessage(message) {
        switch (message.type) {
            case 'process_result':
                this.displayResults(message.payload);
                break;
            case 'verify_result':
                this.displayVerificationResults(message.payload);
                break;
            case 'demo_data':
                this.displayDemoData(message.payload);
                break;
            case 'grid_stats':
                this.displayGridStats(message.payload);
                break;
            case 'error':
                this.displayError(message.payload.error);
                break;
        }
    }

    updateConnectionStatus(connected) {
        const statusIndicator = document.querySelector('.connection-status') || this.createStatusIndicator();
        statusIndicator.textContent = connected ? '🟢 Connected' : '🔴 Disconnected';
        statusIndicator.className = `connection-status ${connected ? 'connected' : 'disconnected'}`;
    }

    createStatusIndicator() {
        const indicator = document.createElement('div');
        indicator.className = 'connection-status';
        indicator.style.cssText = `
            position: fixed;
            top: 20px;
            right: 20px;
            padding: 10px 15px;
            border-radius: 20px;
            font-size: 14px;
            font-weight: 600;
            z-index: 1000;
            background: rgba(255, 255, 255, 0.9);
            box-shadow: 0 2px 10px rgba(0, 0, 0, 0.1);
        `;
        document.body.appendChild(indicator);
        return indicator;
    }

    async processData() {
        if (!this.isConnected) {
            this.displayError('Not connected to server');
            return;
        }

        const content = {
            name: this.dataNameInput.value || 'Demo Data',
            data: this.dataContentInput.value,
            mimeType: this.mimeTypeSelect.value
        };

        if (!content.data.trim()) {
            this.displayError('Please enter some data to process');
            return;
        }

        this.setLoading(true);
        
        try {
            this.ws.send(JSON.stringify({
                type: 'process_content',
                payload: content
            }));
        } catch (error) {
            this.displayError('Failed to send request: ' + error.message);
            this.setLoading(false);
        }
    }

    async verifyDeterministic() {
        if (!this.isConnected) {
            this.displayError('Not connected to server');
            return;
        }

        const content = {
            name: this.dataNameInput.value || 'Demo Data',
            data: this.dataContentInput.value,
            mimeType: this.mimeTypeSelect.value
        };

        if (!content.data.trim()) {
            this.displayError('Please enter some data to verify');
            return;
        }

        this.setLoading(true);
        
        try {
            this.ws.send(JSON.stringify({
                type: 'verify_deterministic',
                payload: { content, iterations: 5 }
            }));
        } catch (error) {
            this.displayError('Failed to send request: ' + error.message);
            this.setLoading(false);
        }
    }

    displayResults(result) {
        this.setLoading(false);
        this.currentResults = result;
        
        // Display main results
        this.resultsContainer.innerHTML = `
            <div class="result-item">
                <div class="result-label">Page (Row):</div>
                <div class="result-value">${result.atlas.page}</div>
            </div>
            <div class="result-item">
                <div class="result-label">Cycle (Column):</div>
                <div class="result-value">${result.atlas.cycle}</div>
            </div>
            <div class="result-item">
                <div class="result-label">R96 Class:</div>
                <div class="result-value">${result.atlas.r96Class}</div>
            </div>
            <div class="result-item">
                <div class="result-label">Klein Window:</div>
                <div class="result-value">${result.atlas.kleinWindow}</div>
            </div>
            <div class="result-item">
                <div class="result-label">Conservation Hash:</div>
                <div class="result-value">${result.atlas.conservationHash}</div>
            </div>
            <div class="result-item">
                <div class="result-label">UOR-ID:</div>
                <div class="result-value">${result.atlas.uorId}</div>
            </div>
        `;
        
        // Update performance metrics
        this.updatePerformanceMetrics(result);
        
        // Update grid visualization
        this.updateGridVisualization(result.atlas);
        
        // Update R96 visualization
        this.updateR96Visualization(result.atlas.r96Class);
        
        // Show success message
        this.showSuccessMessage(`Data processed successfully in ${result.processingTime}ms`);
    }

    displayVerificationResults(result) {
        this.setLoading(false);
        
        const status = result.isDeterministic ? '✅ DETERMINISTIC' : '❌ NOT DETERMINISTIC';
        const consistency = result.consistency;
        
        let resultsHtml = `
            <div class="result-item">
                <div class="result-label">Deterministic Status:</div>
                <div class="result-value ${result.isDeterministic ? 'success' : 'error'}">${status}</div>
            </div>
            <div class="result-item">
                <div class="result-label">Consistency:</div>
                <div class="result-value">${consistency}%</div>
            </div>
            <div class="result-item">
                <div class="result-label">Iterations:</div>
                <div class="result-value">${result.results.length}</div>
            </div>
        `;
        
        // Show all results
        result.results.forEach((res, index) => {
            resultsHtml += `
                <div class="result-item">
                    <div class="result-label">Iteration ${index + 1}:</div>
                    <div class="result-value">Page: ${res.page}, Cycle: ${res.cycle}, R96: ${res.r96Class}</div>
                </div>
            `;
        });
        
        this.resultsContainer.innerHTML = resultsHtml;
        
        if (result.isDeterministic) {
            this.showSuccessMessage('✅ Deterministic mapping verified! Same input always produces same output.');
        } else {
            this.showErrorMessage('❌ Mapping is not deterministic. This should not happen!');
        }
    }

    displayDemoData(demoData) {
        this.demoDataContainer.innerHTML = demoData.map((data, index) => `
            <div class="demo-set" onclick="atlasDemo.loadDemoDataItem(${index})">
                <div class="demo-set-name">${data.name}</div>
                <div class="demo-set-content">${data.data.substring(0, 100)}${data.data.length > 100 ? '...' : ''}</div>
            </div>
        `).join('');
    }

    displayGridStats(stats) {
        this.totalCoordsSpan.textContent = stats.totalCoordinates.toLocaleString();
        this.pagesSpan.textContent = stats.pages;
        this.cyclesSpan.textContent = stats.cycles;
        this.r96ClassesSpan.textContent = stats.r96Classes;
    }

    updatePerformanceMetrics(result) {
        this.processingTimeSpan.textContent = `${result.processingTime}ms`;
        this.dataSizeSpan.textContent = `${result.byteAnalysis.totalBytes} bytes`;
        this.uniqueBytesSpan.textContent = `${result.byteAnalysis.uniqueBytes} unique`;
        this.entropySpan.textContent = result.byteAnalysis.entropy.toFixed(2);
    }

    updateGridVisualization(atlas) {
        // Clear previous highlights
        this.gridCells.forEach(cell => {
            cell.classList.remove('highlighted', 'r96-highlighted');
        });
        
        // Create grid if not exists
        if (this.gridCells.length === 0) {
            this.createGrid();
        }
        
        // Highlight the coordinate
        const cellIndex = atlas.page * 256 + atlas.cycle;
        if (this.gridCells[cellIndex]) {
            this.gridCells[cellIndex].classList.add('highlighted');
        }
        
        // Add tooltip
        this.gridCells.forEach((cell, index) => {
            const page = Math.floor(index / 256);
            const cycle = index % 256;
            cell.title = `Page: ${page}, Cycle: ${cycle}`;
        });
    }

    createGrid() {
        this.gridContainer.innerHTML = '';
        this.gridCells = [];
        
        for (let i = 0; i < 12288; i++) {
            const cell = document.createElement('div');
            cell.className = 'grid-cell';
            this.gridContainer.appendChild(cell);
            this.gridCells.push(cell);
        }
    }

    updateR96Visualization(r96Class) {
        this.r96Container.innerHTML = `
            <div class="r96-header">
                <h3>Data classified into R96 Class: <strong>${r96Class}</strong></h3>
                <p>Out of 96 possible equivalence classes (0-95)</p>
            </div>
            <div class="r96-classes">
                ${Array.from({length: 96}, (_, i) => `
                    <div class="r96-class ${i === r96Class ? 'active' : ''}">
                        ${i}
                    </div>
                `).join('')}
            </div>
        `;
    }

    loadDemoData() {
        if (this.isConnected) {
            this.ws.send(JSON.stringify({ type: 'get_demo_data' }));
        }
    }

    loadGridStats() {
        if (this.isConnected) {
            this.ws.send(JSON.stringify({ type: 'get_grid_stats' }));
        }
    }

    loadDemoDataItem(index) {
        // This would be implemented to load specific demo data
        console.log('Loading demo data item:', index);
    }

    setLoading(loading) {
        this.processBtn.disabled = loading;
        this.verifyBtn.disabled = loading;
        
        if (loading) {
            this.processBtn.innerHTML = '<span class="loading"></span> Processing...';
            this.verifyBtn.innerHTML = '<span class="loading"></span> Verifying...';
        } else {
            this.processBtn.innerHTML = '🚀 Process Data';
            this.verifyBtn.innerHTML = '🔍 Verify Deterministic';
        }
    }

    displayError(message) {
        this.setLoading(false);
        this.showErrorMessage(message);
    }

    showSuccessMessage(message) {
        this.showMessage(message, 'success');
    }

    showErrorMessage(message) {
        this.showMessage(message, 'error');
    }

    showMessage(message, type) {
        const messageDiv = document.createElement('div');
        messageDiv.className = `message ${type}`;
        messageDiv.textContent = message;
        messageDiv.style.cssText = `
            position: fixed;
            top: 80px;
            right: 20px;
            padding: 15px 20px;
            border-radius: 8px;
            color: white;
            font-weight: 600;
            z-index: 1000;
            max-width: 300px;
            box-shadow: 0 3px 10px rgba(0, 0, 0, 0.2);
            background: ${type === 'success' ? '#28a745' : '#dc3545'};
        `;
        
        document.body.appendChild(messageDiv);
        
        setTimeout(() => {
            messageDiv.remove();
        }, 5000);
    }
}

// Initialize the demo when the page loads
let atlasDemo;
document.addEventListener('DOMContentLoaded', () => {
    atlasDemo = new AtlasDemoClient();
});

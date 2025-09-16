/**
 * Atlas-12288 Web Demo Server
 * 
 * Interactive web interface for demonstrating Atlas functionality
 */

const express = require('express');
const path = require('path');
const WebSocket = require('ws');
const { AtlasDemoEngine } = require('../src/AtlasDemoEngine');

const app = express();
const PORT = 3000;

// Serve static files
app.use(express.static(path.join(__dirname, 'public')));
app.use(express.json());

// Initialize Atlas demo engine
const atlasEngine = new AtlasDemoEngine();

// WebSocket server for real-time updates
const server = require('http').createServer(app);
const wss = new WebSocket.Server({ server });

// WebSocket connection handling
wss.on('connection', (ws) => {
  console.log('Client connected to Atlas demo');
  
  ws.on('message', async (message) => {
    try {
      const data = JSON.parse(message);
      
      switch (data.type) {
        case 'process_content':
          await handleProcessContent(ws, data.payload);
          break;
        case 'verify_deterministic':
          await handleVerifyDeterministic(ws, data.payload);
          break;
        case 'get_demo_data':
          await handleGetDemoData(ws);
          break;
        case 'get_grid_stats':
          await handleGetGridStats(ws);
          break;
        default:
          ws.send(JSON.stringify({ error: 'Unknown message type' }));
      }
    } catch (error) {
      ws.send(JSON.stringify({ error: error.message }));
    }
  });
  
  ws.on('close', () => {
    console.log('Client disconnected from Atlas demo');
  });
});

// API endpoints
app.get('/api/grid-stats', (req, res) => {
  const stats = atlasEngine.getGridStatistics();
  res.json(stats);
});

app.get('/api/demo-data', (req, res) => {
  const demoData = atlasEngine.generateDemoData();
  res.json(demoData);
});

app.post('/api/process', async (req, res) => {
  try {
    const result = await atlasEngine.processContent(req.body);
    res.json(result);
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.post('/api/verify-deterministic', async (req, res) => {
  try {
    const { content, iterations = 5 } = req.body;
    const result = await atlasEngine.verifyDeterministicMapping(content, iterations);
    res.json(result);
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// WebSocket handlers
async function handleProcessContent(ws, payload) {
  try {
    const result = await atlasEngine.processContent(payload);
    ws.send(JSON.stringify({
      type: 'process_result',
      payload: result
    }));
  } catch (error) {
    ws.send(JSON.stringify({
      type: 'error',
      payload: { error: error.message }
    }));
  }
}

async function handleVerifyDeterministic(ws, payload) {
  try {
    const { content, iterations = 5 } = payload;
    const result = await atlasEngine.verifyDeterministicMapping(content, iterations);
    ws.send(JSON.stringify({
      type: 'verify_result',
      payload: result
    }));
  } catch (error) {
    ws.send(JSON.stringify({
      type: 'error',
      payload: { error: error.message }
    }));
  }
}

async function handleGetDemoData(ws) {
  try {
    const demoData = atlasEngine.generateDemoData();
    ws.send(JSON.stringify({
      type: 'demo_data',
      payload: demoData
    }));
  } catch (error) {
    ws.send(JSON.stringify({
      type: 'error',
      payload: { error: error.message }
    }));
  }
}

async function handleGetGridStats(ws) {
  try {
    const stats = atlasEngine.getGridStatistics();
    ws.send(JSON.stringify({
      type: 'grid_stats',
      payload: stats
    }));
  } catch (error) {
    ws.send(JSON.stringify({
      type: 'error',
      payload: { error: error.message }
    }));
  }
}

// Start server
server.listen(PORT, () => {
  console.log(`🚀 Atlas-12288 Demo Server running on http://localhost:${PORT}`);
  console.log(`📊 WebSocket server ready for real-time updates`);
  console.log(`🎯 Demo features:`);
  console.log(`   - 96 Equivalence Classes (R96)`);
  console.log(`   - 12,288 Coordinates (48×256 grid)`);
  console.log(`   - Real-time data processing`);
  console.log(`   - Deterministic mapping verification`);
});

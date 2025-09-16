#!/usr/bin/env node

/**
 * Working Atlas Demo
 */

const crypto = require('crypto');

class AtlasDemoEngine {
    constructor() {
        this.N = 12288; // Total elements
        this.P = 48;    // Pages (rows)
        this.C = 256;   // Cycles (columns)
        this.R = 96;    // R96 classes
    }

    generateCoordinates(content) {
        const contentHash = crypto.createHash('sha256').update(content.data).digest('hex');
        const hashBytes = Buffer.from(contentHash, 'hex');
        
        const pageHash = hashBytes.readUInt32BE(0);
        const page = pageHash % this.P;
        
        const cycleHash = hashBytes.readUInt32BE(4);
        const cycle = cycleHash % this.C;
        
        return { page, cycle };
    }

    classifyContent(content) {
        const dataBytes = Buffer.from(content.data, 'utf8');
        const byteArray = Array.from(dataBytes);
        
        let acc = 0;
        for (const v of byteArray) {
            acc = (acc + (v | 0)) % this.R;
        }
        
        return (acc + this.R) % this.R;
    }

    selectKleinWindow(content) {
        const hash = crypto.createHash('sha256').update(content.data).digest('hex');
        const hashBytes = Buffer.from(hash, 'hex');
        return hashBytes.readUInt32BE(8) % 192;
    }

    generateConservationHash(content, coordinates) {
        const input = `${content.data}:${coordinates.page}:${coordinates.cycle}`;
        return crypto.createHash('sha256').update(input).digest('hex').substring(0, 16);
    }

    generateUORID(content, coordinates, r96Class) {
        const input = `${content.name}:${content.data}:${coordinates.page}:${coordinates.cycle}:${r96Class}`;
        return crypto.createHash('sha256').update(input).digest('hex').substring(0, 32);
    }

    analyzeBytes(data) {
        const bytes = Buffer.from(data, 'utf8');
        const byteArray = Array.from(bytes);
        
        const uniqueBytes = new Set(byteArray).size;
        
        const byteCounts = new Map();
        for (const byte of byteArray) {
            byteCounts.set(byte, (byteCounts.get(byte) || 0) + 1);
        }
        
        let entropy = 0;
        const totalBytes = byteArray.length;
        for (const count of byteCounts.values()) {
            const probability = count / totalBytes;
            entropy -= probability * Math.log2(probability);
        }
        
        let acc = 0;
        for (const v of byteArray) {
            acc = (acc + (v | 0)) % this.R;
        }
        const r96Classification = (acc + this.R) % this.R;
        
        return {
            totalBytes,
            uniqueBytes,
            entropy,
            r96Classification
        };
    }

    async processContent(content) {
        const startTime = Date.now();
        
        const coordinates = this.generateCoordinates(content);
        const r96Class = this.classifyContent(content);
        const kleinWindow = this.selectKleinWindow(content);
        const conservationHash = this.generateConservationHash(content, coordinates);
        const uorId = this.generateUORID(content, coordinates, r96Class);
        
        const atlas = {
            page: coordinates.page,
            cycle: coordinates.cycle,
            r96Class,
            kleinWindow,
            conservationHash,
            uorId
        };
        
        const byteAnalysis = this.analyzeBytes(content.data);
        const processingTime = Date.now() - startTime;
        
        return {
            input: content,
            atlas,
            processingTime,
            byteAnalysis
        };
    }

    generateDemoData() {
        return [
            {
                name: "Simple Text",
                data: "Hello, Atlas World!",
                mimeType: "text/plain"
            },
            {
                name: "JSON Data",
                data: JSON.stringify({
                    id: 1,
                    name: "Demo User",
                    email: "demo@atlas.com",
                    active: true
                }),
                mimeType: "application/json"
            },
            {
                name: "Long Text",
                data: "Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.",
                mimeType: "text/plain"
            },
            {
                name: "Binary-like Data",
                data: Buffer.from([0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x57, 0x6F, 0x72, 0x6C, 0x64]).toString('utf8'),
                mimeType: "application/octet-stream"
            },
            {
                name: "Unicode Text",
                data: "🌍 Atlas-12288 世界地图 🗺️",
                mimeType: "text/plain"
            }
        ];
    }

    getGridStatistics() {
        return {
            totalCoordinates: this.N,
            pages: this.P,
            cycles: this.C,
            r96Classes: this.R,
            gridDimensions: `${this.P}×${this.C}`
        };
    }

    async verifyDeterministicMapping(content, iterations = 5) {
        const results = [];
        
        for (let i = 0; i < iterations; i++) {
            const result = await this.processContent(content);
            results.push(result.atlas);
        }
        
        const firstResult = results[0];
        const isDeterministic = results.every(result => 
            result.page === firstResult.page &&
            result.cycle === firstResult.cycle &&
            result.r96Class === firstResult.r96Class &&
            result.conservationHash === firstResult.conservationHash &&
            result.uorId === firstResult.uorId
        );
        
        const consistency = isDeterministic ? 100 : 0;
        
        return {
            isDeterministic,
            results,
            consistency
        };
    }
}

async function runDemo() {
    console.log('🚀 Atlas-12288 Working Demo');
    console.log('=' .repeat(50));
    
    const engine = new AtlasDemoEngine();
    
    // Test 1: Basic Processing
    console.log('\n📝 1. Basic Data Processing');
    const testData = {
        name: 'Demo Data',
        data: 'Hello, Atlas World!',
        mimeType: 'text/plain'
    };
    
    const result = await engine.processContent(testData);
    console.log('Input:', testData);
    console.log('Results:');
    console.log(`  Page: ${result.atlas.page}`);
    console.log(`  Cycle: ${result.atlas.cycle}`);
    console.log(`  R96 Class: ${result.atlas.r96Class}`);
    console.log(`  Klein Window: ${result.atlas.kleinWindow}`);
    console.log(`  Conservation Hash: ${result.atlas.conservationHash}`);
    console.log(`  UOR-ID: ${result.atlas.uorId}`);
    console.log(`  Processing Time: ${result.processingTime}ms`);
    
    // Test 2: Deterministic Mapping
    console.log('\n🔍 2. Deterministic Mapping Verification');
    const verification = await engine.verifyDeterministicMapping(testData, 5);
    console.log(`Deterministic: ${verification.isDeterministic ? '✅ YES' : '❌ NO'}`);
    console.log(`Consistency: ${verification.consistency}%`);
    
    // Test 3: Demo Data Sets
    console.log('\n📋 3. Demo Data Sets');
    const demoData = engine.generateDemoData();
    console.log(`Generated ${demoData.length} demo data sets:`);
    
    for (const data of demoData) {
        const result = await engine.processContent(data);
        console.log(`  ${data.name}: Page=${result.atlas.page}, Cycle=${result.atlas.cycle}, R96=${result.atlas.r96Class}`);
    }
    
    // Test 4: Grid Statistics
    console.log('\n📊 4. Grid Statistics');
    const stats = engine.getGridStatistics();
    console.log(`Total Coordinates: ${stats.totalCoordinates.toLocaleString()}`);
    console.log(`Grid Dimensions: ${stats.gridDimensions}`);
    console.log(`Pages: ${stats.pages}`);
    console.log(`Cycles: ${stats.cycles}`);
    console.log(`R96 Classes: ${stats.r96Classes}`);
    
    console.log('\n🎉 Demo completed successfully!');
    console.log('\nKey Insights:');
    console.log('• Every piece of data maps to exactly one coordinate in the 48×256 grid');
    console.log('• Data collapses into exactly 96 equivalence classes (R96)');
    console.log('• Mapping is completely deterministic and reproducible');
    console.log('• Processing is fast and efficient');
}

runDemo().catch(console.error);

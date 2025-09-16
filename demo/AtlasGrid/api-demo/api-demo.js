#!/usr/bin/env node

/**
 * Atlas-12288 API Demo
 * 
 * Demonstrates the Atlas API functionality programmatically
 */

const { AtlasDemoEngine } = require('../dist/AtlasDemoEngine');

class AtlasAPIDemo {
    constructor() {
        this.atlasEngine = new AtlasDemoEngine();
    }

    async runDemo() {
        console.log('🚀 Atlas-12288 API Demo Starting...\n');
        
        try {
            await this.demonstrateBasicProcessing();
            await this.demonstrateDeterministicMapping();
            await this.demonstrateR96Classification();
            await this.demonstrateGridMapping();
            await this.demonstratePerformance();
            await this.demonstrateBatchProcessing();
            
            console.log('\n✅ Atlas-12288 API Demo Completed Successfully!');
        } catch (error) {
            console.error('\n❌ Demo failed:', error.message);
            process.exit(1);
        }
    }

    async demonstrateBasicProcessing() {
        console.log('📝 1. Basic Data Processing');
        console.log('=' .repeat(50));
        
        const testData = {
            name: 'API Demo Data',
            data: 'Hello, Atlas API World!',
            mimeType: 'text/plain'
        };

        console.log('Input:', testData);
        
        const result = await this.atlasEngine.processContent(testData);
        
        console.log('\nAtlas Results:');
        console.log(`  Page: ${result.atlas.page}`);
        console.log(`  Cycle: ${result.atlas.cycle}`);
        console.log(`  R96 Class: ${result.atlas.r96Class}`);
        console.log(`  Klein Window: ${result.atlas.kleinWindow}`);
        console.log(`  Conservation Hash: ${result.atlas.conservationHash}`);
        console.log(`  UOR-ID: ${result.atlas.uorId}`);
        console.log(`  Processing Time: ${result.processingTime}ms`);
        
        console.log('\nByte Analysis:');
        console.log(`  Total Bytes: ${result.byteAnalysis.totalBytes}`);
        console.log(`  Unique Bytes: ${result.byteAnalysis.uniqueBytes}`);
        console.log(`  Entropy: ${result.byteAnalysis.entropy.toFixed(2)}`);
        console.log(`  R96 Classification: ${result.byteAnalysis.r96Classification}`);
        
        console.log('\n');
    }

    async demonstrateDeterministicMapping() {
        console.log('🔍 2. Deterministic Mapping Verification');
        console.log('=' .repeat(50));
        
        const testData = {
            name: 'Deterministic Test',
            data: 'This data should always map to the same coordinates',
            mimeType: 'text/plain'
        };

        console.log('Testing deterministic mapping with 5 iterations...');
        
        const verification = await this.atlasEngine.verifyDeterministicMapping(testData, 5);
        
        console.log(`\nDeterministic: ${verification.isDeterministic ? '✅ YES' : '❌ NO'}`);
        console.log(`Consistency: ${verification.consistency}%`);
        console.log(`Iterations: ${verification.results.length}`);
        
        console.log('\nAll Results:');
        verification.results.forEach((result, index) => {
            console.log(`  Iteration ${index + 1}: Page=${result.page}, Cycle=${result.cycle}, R96=${result.r96Class}`);
        });
        
        if (verification.isDeterministic) {
            console.log('\n✅ Perfect! Atlas mapping is completely deterministic.');
        } else {
            console.log('\n⚠️  Warning: Mapping is not deterministic!');
        }
        
        console.log('\n');
    }

    async demonstrateR96Classification() {
        console.log('🎯 3. R96 Classification Analysis');
        console.log('=' .repeat(50));
        
        const testDataSets = [
            { name: 'Text Data', data: 'Hello World', mimeType: 'text/plain' },
            { name: 'JSON Data', data: JSON.stringify({ id: 1, name: 'test' }), mimeType: 'application/json' },
            { name: 'Binary-like', data: Buffer.from([0x48, 0x65, 0x6C, 0x6C, 0x6F]).toString('utf8'), mimeType: 'application/octet-stream' },
            { name: 'Unicode', data: '🌍 Atlas 世界', mimeType: 'text/plain' },
            { name: 'Numbers', data: '1234567890', mimeType: 'text/plain' }
        ];

        console.log('Analyzing R96 classification for different data types:\n');
        
        const results = [];
        for (const testData of testDataSets) {
            const result = await this.atlasEngine.processContent(testData);
            results.push({
                name: testData.name,
                r96Class: result.atlas.r96Class,
                totalBytes: result.byteAnalysis.totalBytes,
                uniqueBytes: result.byteAnalysis.uniqueBytes,
                entropy: result.byteAnalysis.entropy
            });
        }

        console.log('R96 Classification Results:');
        console.log('┌─────────────┬─────────┬──────────┬─────────────┬─────────┐');
        console.log('│ Data Type   │ R96     │ Total    │ Unique      │ Entropy │');
        console.log('│             │ Class   │ Bytes    │ Bytes       │         │');
        console.log('├─────────────┼─────────┼──────────┼─────────────┼─────────┤');
        
        results.forEach(result => {
            const name = result.name.padEnd(11);
            const r96 = result.r96Class.toString().padStart(7);
            const total = result.totalBytes.toString().padStart(8);
            const unique = result.uniqueBytes.toString().padStart(11);
            const entropy = result.entropy.toFixed(2).padStart(7);
            
            console.log(`│ ${name} │ ${r96} │ ${total} │ ${unique} │ ${entropy} │`);
        });
        
        console.log('└─────────────┴─────────┴──────────┴─────────────┴─────────┘');
        
        // Show R96 class distribution
        const classCounts = new Map();
        results.forEach(result => {
            classCounts.set(result.r96Class, (classCounts.get(result.r96Class) || 0) + 1);
        });
        
        console.log('\nR96 Class Distribution:');
        for (let i = 0; i < 96; i++) {
            const count = classCounts.get(i) || 0;
            if (count > 0) {
                console.log(`  Class ${i}: ${count} data set(s)`);
            }
        }
        
        console.log('\n');
    }

    async demonstrateGridMapping() {
        console.log('🗺️  4. Grid Coordinate Mapping');
        console.log('=' .repeat(50));
        
        const testData = {
            name: 'Grid Mapping Test',
            data: 'Mapping this data to Atlas grid coordinates',
            mimeType: 'text/plain'
        };

        const result = await this.atlasEngine.processContent(testData);
        const gridStats = this.atlasEngine.getGridStatistics();
        
        console.log('Grid Statistics:');
        console.log(`  Total Coordinates: ${gridStats.totalCoordinates.toLocaleString()}`);
        console.log(`  Grid Dimensions: ${gridStats.gridDimensions}`);
        console.log(`  Pages (Rows): ${gridStats.pages}`);
        console.log(`  Cycles (Columns): ${gridStats.cycles}`);
        console.log(`  R96 Classes: ${gridStats.r96Classes}`);
        
        console.log('\nData Mapping:');
        console.log(`  Input Data: "${testData.data}"`);
        console.log(`  Mapped to Page: ${result.atlas.page} (row ${result.atlas.page + 1} of ${gridStats.pages})`);
        console.log(`  Mapped to Cycle: ${result.atlas.cycle} (column ${result.atlas.cycle + 1} of ${gridStats.cycles})`);
        console.log(`  Grid Index: ${result.atlas.page * 256 + result.atlas.cycle}`);
        console.log(`  R96 Class: ${result.atlas.r96Class} (out of ${gridStats.r96Classes} classes)`);
        
        // Verify coordinate calculation
        const calculatedIndex = result.atlas.page * 256 + result.atlas.cycle;
        const calculatedPage = Math.floor(calculatedIndex / 256);
        const calculatedCycle = calculatedIndex % 256;
        
        console.log('\nCoordinate Verification:');
        console.log(`  Calculated Index: ${calculatedIndex}`);
        console.log(`  Calculated Page: ${calculatedPage} (matches: ${calculatedPage === result.atlas.page})`);
        console.log(`  Calculated Cycle: ${calculatedCycle} (matches: ${calculatedCycle === result.atlas.cycle})`);
        
        console.log('\n');
    }

    async demonstratePerformance() {
        console.log('⚡ 5. Performance Analysis');
        console.log('=' .repeat(50));
        
        const testData = {
            name: 'Performance Test',
            data: 'Performance testing data for Atlas system',
            mimeType: 'text/plain'
        };

        const iterations = 100;
        const times = [];
        
        console.log(`Running ${iterations} iterations for performance analysis...`);
        
        for (let i = 0; i < iterations; i++) {
            const start = process.hrtime.bigint();
            await this.atlasEngine.processContent(testData);
            const end = process.hrtime.bigint();
            times.push(Number(end - start) / 1000000); // Convert to milliseconds
        }
        
        const avgTime = times.reduce((a, b) => a + b, 0) / times.length;
        const minTime = Math.min(...times);
        const maxTime = Math.max(...times);
        const medianTime = times.sort((a, b) => a - b)[Math.floor(times.length / 2)];
        
        console.log('\nPerformance Results:');
        console.log(`  Average Time: ${avgTime.toFixed(3)}ms`);
        console.log(`  Minimum Time: ${minTime.toFixed(3)}ms`);
        console.log(`  Maximum Time: ${maxTime.toFixed(3)}ms`);
        console.log(`  Median Time: ${medianTime.toFixed(3)}ms`);
        console.log(`  Total Time: ${times.reduce((a, b) => a + b, 0).toFixed(3)}ms`);
        
        // Calculate throughput
        const throughput = (1000 / avgTime).toFixed(0);
        console.log(`  Throughput: ~${throughput} operations/second`);
        
        console.log('\n');
    }

    async demonstrateBatchProcessing() {
        console.log('📦 6. Batch Processing Demo');
        console.log('=' .repeat(50));
        
        const demoData = this.atlasEngine.generateDemoData();
        console.log(`Processing ${demoData.length} demo data sets in batch...\n`);
        
        const startTime = Date.now();
        const results = [];
        
        for (const data of demoData) {
            const result = await this.atlasEngine.processContent(data);
            results.push(result);
        }
        
        const totalTime = Date.now() - startTime;
        const avgTime = totalTime / results.length;
        
        console.log('Batch Processing Results:');
        console.log(`  Total Data Sets: ${results.length}`);
        console.log(`  Total Time: ${totalTime}ms`);
        console.log(`  Average Time per Set: ${avgTime.toFixed(2)}ms`);
        console.log(`  Throughput: ${(results.length / (totalTime / 1000)).toFixed(2)} sets/second`);
        
        console.log('\nIndividual Results:');
        console.log('┌─────────────────┬──────┬───────┬─────────┬──────────┐');
        console.log('│ Data Set        │ Page │ Cycle │ R96     │ Time(ms) │');
        console.log('├─────────────────┼──────┼───────┼─────────┼──────────┤');
        
        results.forEach((result, index) => {
            const name = demoData[index].name.padEnd(15);
            const page = result.atlas.page.toString().padStart(4);
            const cycle = result.atlas.cycle.toString().padStart(5);
            const r96 = result.atlas.r96Class.toString().padStart(7);
            const time = result.processingTime.toString().padStart(8);
            
            console.log(`│ ${name} │ ${page} │ ${cycle} │ ${r96} │ ${time} │`);
        });
        
        console.log('└─────────────────┴──────┴───────┴─────────┴──────────┘');
        
        // Analyze coordinate distribution
        const pageCounts = new Map();
        const cycleCounts = new Map();
        const r96Counts = new Map();
        
        results.forEach(result => {
            pageCounts.set(result.atlas.page, (pageCounts.get(result.atlas.page) || 0) + 1);
            cycleCounts.set(result.atlas.cycle, (cycleCounts.get(result.atlas.cycle) || 0) + 1);
            r96Counts.set(result.atlas.r96Class, (r96Counts.get(result.atlas.r96Class) || 0) + 1);
        });
        
        console.log('\nDistribution Analysis:');
        console.log(`  Unique Pages Used: ${pageCounts.size} out of 48`);
        console.log(`  Unique Cycles Used: ${cycleCounts.size} out of 256`);
        console.log(`  Unique R96 Classes: ${r96Counts.size} out of 96`);
        
        console.log('\n');
    }
}

// Run the demo
if (require.main === module) {
    const demo = new AtlasAPIDemo();
    demo.runDemo().catch(console.error);
}

module.exports = AtlasAPIDemo;

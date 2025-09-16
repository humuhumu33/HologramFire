#!/usr/bin/env node

/**
 * Simple Atlas Demo Test
 */

const { AtlasDemoEngine } = require('./dist/AtlasDemoEngine');

async function runSimpleTest() {
    console.log('🚀 Starting Simple Atlas Demo Test...\n');
    
    try {
        const engine = new AtlasDemoEngine();
        console.log('✅ AtlasDemoEngine created successfully');
        
        const testData = {
            name: 'Simple Test',
            data: 'Hello, Atlas World!',
            mimeType: 'text/plain'
        };
        
        console.log('📝 Processing test data...');
        const result = await engine.processContent(testData);
        
        console.log('\n📊 Results:');
        console.log(`  Page: ${result.atlas.page}`);
        console.log(`  Cycle: ${result.atlas.cycle}`);
        console.log(`  R96 Class: ${result.atlas.r96Class}`);
        console.log(`  Processing Time: ${result.processingTime}ms`);
        
        console.log('\n🎯 Testing deterministic mapping...');
        const verification = await engine.verifyDeterministicMapping(testData, 3);
        console.log(`  Deterministic: ${verification.isDeterministic ? '✅ YES' : '❌ NO'}`);
        console.log(`  Consistency: ${verification.consistency}%`);
        
        console.log('\n📋 Testing demo data generation...');
        const demoData = engine.generateDemoData();
        console.log(`  Generated ${demoData.length} demo data sets`);
        
        console.log('\n📊 Testing grid statistics...');
        const stats = engine.getGridStatistics();
        console.log(`  Total Coordinates: ${stats.totalCoordinates}`);
        console.log(`  Grid Dimensions: ${stats.gridDimensions}`);
        console.log(`  R96 Classes: ${stats.r96Classes}`);
        
        console.log('\n🎉 Simple test completed successfully!');
        
    } catch (error) {
        console.error('\n❌ Test failed:', error.message);
        console.error(error.stack);
        process.exit(1);
    }
}

runSimpleTest();

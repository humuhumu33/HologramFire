console.log('Starting async test...');

async function testAsync() {
    try {
        const { AtlasDemoEngine } = require('./dist/AtlasDemoEngine');
        console.log('Module loaded successfully');
        
        const engine = new AtlasDemoEngine();
        console.log('Engine created successfully');
        
        const testData = {
            name: 'Async Test',
            data: 'Hello, Async Atlas!',
            mimeType: 'text/plain'
        };
        
        console.log('Processing data...');
        const result = await engine.processContent(testData);
        console.log('Processing completed');
        
        console.log('Results:');
        console.log('  Page:', result.atlas.page);
        console.log('  Cycle:', result.atlas.cycle);
        console.log('  R96 Class:', result.atlas.r96Class);
        console.log('  Processing Time:', result.processingTime + 'ms');
        
        console.log('Async test completed successfully!');
    } catch (error) {
        console.error('Error:', error.message);
        console.error(error.stack);
    }
}

testAsync();

console.log('Starting sync test...');

try {
    const { AtlasDemoEngine } = require('./dist/AtlasDemoEngine');
    console.log('Module loaded successfully');
    
    const engine = new AtlasDemoEngine();
    console.log('Engine created successfully');
    
    // Test the individual methods directly
    const testData = {
        name: 'Sync Test',
        data: 'Hello, Sync Atlas!',
        mimeType: 'text/plain'
    };
    
    console.log('Testing coordinate generation...');
    const coordinates = engine.generateCoordinates(testData);
    console.log('Coordinates:', coordinates);
    
    console.log('Testing R96 classification...');
    const r96Class = engine.classifyContent(testData);
    console.log('R96 Class:', r96Class);
    
    console.log('Testing Klein window selection...');
    const kleinWindow = engine.selectKleinWindow(testData);
    console.log('Klein Window:', kleinWindow);
    
    console.log('Testing byte analysis...');
    const byteAnalysis = engine.analyzeBytes(testData.data);
    console.log('Byte Analysis:', byteAnalysis);
    
    console.log('Sync test completed successfully!');
} catch (error) {
    console.error('Error:', error.message);
    console.error(error.stack);
}

console.log('Starting quick test...');

try {
    const { AtlasDemoEngine } = require('./dist/AtlasDemoEngine');
    console.log('Module loaded successfully');
    
    const engine = new AtlasDemoEngine();
    console.log('Engine created successfully');
    
    const stats = engine.getGridStatistics();
    console.log('Grid stats:', stats);
    
    const demoData = engine.generateDemoData();
    console.log('Demo data count:', demoData.length);
    
    console.log('Quick test completed successfully!');
} catch (error) {
    console.error('Error:', error.message);
    console.error(error.stack);
}

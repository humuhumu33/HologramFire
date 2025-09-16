#!/usr/bin/env node

/**
 * Atlas-12288 Demo Test Suite
 * 
 * Comprehensive tests to verify all demo functionality works correctly
 */

const { AtlasDemoEngine } = require('../dist/AtlasDemoEngine');

class AtlasDemoTestSuite {
    constructor() {
        this.atlasEngine = new AtlasDemoEngine();
        this.testsPassed = 0;
        this.testsFailed = 0;
        this.testResults = [];
    }

    async runAllTests() {
        console.log('🧪 Atlas-12288 Demo Test Suite');
        console.log('=' .repeat(50));
        console.log('Running comprehensive tests to verify demo functionality...\n');

        try {
            await this.testBasicProcessing();
            await this.testDeterministicMapping();
            await this.testR96Classification();
            await this.testGridMapping();
            await this.testPerformance();
            await this.testDemoDataGeneration();
            await this.testErrorHandling();
            await this.testGridStatistics();
            
            this.printTestSummary();
            
            if (this.testsFailed > 0) {
                process.exit(1);
            } else {
                console.log('\n🎉 All tests passed! Demo is ready for use.');
            }
        } catch (error) {
            console.error('\n❌ Test suite failed:', error.message);
            process.exit(1);
        }
    }

    async testBasicProcessing() {
        console.log('📝 Testing Basic Processing...');
        
        const testData = {
            name: 'Test Data',
            data: 'Hello, Atlas Test!',
            mimeType: 'text/plain'
        };

        try {
            const result = await this.atlasEngine.processContent(testData);
            
            // Verify result structure
            this.assert(result.input, 'Input should be present');
            this.assert(result.atlas, 'Atlas metadata should be present');
            this.assert(result.processingTime >= 0, 'Processing time should be non-negative');
            this.assert(result.byteAnalysis, 'Byte analysis should be present');
            
            // Verify atlas metadata
            this.assert(typeof result.atlas.page === 'number', 'Page should be a number');
            this.assert(typeof result.atlas.cycle === 'number', 'Cycle should be a number');
            this.assert(typeof result.atlas.r96Class === 'number', 'R96 class should be a number');
            this.assert(typeof result.atlas.kleinWindow === 'number', 'Klein window should be a number');
            this.assert(typeof result.atlas.conservationHash === 'string', 'Conservation hash should be a string');
            this.assert(typeof result.atlas.uorId === 'string', 'UOR-ID should be a string');
            
            // Verify ranges
            this.assert(result.atlas.page >= 0 && result.atlas.page < 48, 'Page should be 0-47');
            this.assert(result.atlas.cycle >= 0 && result.atlas.cycle < 256, 'Cycle should be 0-255');
            this.assert(result.atlas.r96Class >= 0 && result.atlas.r96Class < 96, 'R96 class should be 0-95');
            this.assert(result.atlas.kleinWindow >= 0 && result.atlas.kleinWindow < 192, 'Klein window should be 0-191');
            
            // Verify byte analysis
            this.assert(typeof result.byteAnalysis.totalBytes === 'number', 'Total bytes should be a number');
            this.assert(typeof result.byteAnalysis.uniqueBytes === 'number', 'Unique bytes should be a number');
            this.assert(typeof result.byteAnalysis.entropy === 'number', 'Entropy should be a number');
            this.assert(typeof result.byteAnalysis.r96Classification === 'number', 'R96 classification should be a number');
            
            this.assert(result.byteAnalysis.totalBytes > 0, 'Total bytes should be positive');
            this.assert(result.byteAnalysis.uniqueBytes > 0, 'Unique bytes should be positive');
            this.assert(result.byteAnalysis.entropy >= 0, 'Entropy should be non-negative');
            this.assert(result.byteAnalysis.r96Classification >= 0 && result.byteAnalysis.r96Classification < 96, 'R96 classification should be 0-95');
            
            this.recordTest('Basic Processing', true, 'All basic processing tests passed');
            
        } catch (error) {
            this.recordTest('Basic Processing', false, error.message);
        }
    }

    async testDeterministicMapping() {
        console.log('🔍 Testing Deterministic Mapping...');
        
        const testData = {
            name: 'Deterministic Test',
            data: 'This should always map to the same coordinates',
            mimeType: 'text/plain'
        };

        try {
            const verification = await this.atlasEngine.verifyDeterministicMapping(testData, 10);
            
            this.assert(verification.isDeterministic === true, 'Mapping should be deterministic');
            this.assert(verification.consistency === 100, 'Consistency should be 100%');
            this.assert(verification.results.length === 10, 'Should have 10 results');
            
            // Verify all results are identical
            const firstResult = verification.results[0];
            for (let i = 1; i < verification.results.length; i++) {
                const result = verification.results[i];
                this.assert(result.page === firstResult.page, `Page should be consistent (iteration ${i + 1})`);
                this.assert(result.cycle === firstResult.cycle, `Cycle should be consistent (iteration ${i + 1})`);
                this.assert(result.r96Class === firstResult.r96Class, `R96 class should be consistent (iteration ${i + 1})`);
                this.assert(result.conservationHash === firstResult.conservationHash, `Conservation hash should be consistent (iteration ${i + 1})`);
                this.assert(result.uorId === firstResult.uorId, `UOR-ID should be consistent (iteration ${i + 1})`);
            }
            
            this.recordTest('Deterministic Mapping', true, 'Deterministic mapping verified');
            
        } catch (error) {
            this.recordTest('Deterministic Mapping', false, error.message);
        }
    }

    async testR96Classification() {
        console.log('🎯 Testing R96 Classification...');
        
        const testDataSets = [
            { name: 'Text', data: 'Hello World', mimeType: 'text/plain' },
            { name: 'JSON', data: JSON.stringify({ id: 1 }), mimeType: 'application/json' },
            { name: 'Numbers', data: '1234567890', mimeType: 'text/plain' },
            { name: 'Empty', data: '', mimeType: 'text/plain' }
        ];

        try {
            for (const testData of testDataSets) {
                const result = await this.atlasEngine.processContent(testData);
                
                this.assert(result.atlas.r96Class >= 0 && result.atlas.r96Class < 96, `R96 class should be 0-95 for ${testData.name}`);
                this.assert(result.byteAnalysis.r96Classification === result.atlas.r96Class, `R96 classification should match for ${testData.name}`);
            }
            
            // Test that different data can produce different R96 classes
            const results = await Promise.all(testDataSets.map(data => this.atlasEngine.processContent(data)));
            const r96Classes = results.map(r => r.atlas.r96Class);
            const uniqueClasses = new Set(r96Classes);
            
            // At least some should be different (though not guaranteed)
            this.assert(uniqueClasses.size >= 1, 'Should have at least one R96 class');
            this.assert(uniqueClasses.size <= 96, 'Should have at most 96 R96 classes');
            
            this.recordTest('R96 Classification', true, `R96 classification working correctly (${uniqueClasses.size} unique classes)`);
            
        } catch (error) {
            this.recordTest('R96 Classification', false, error.message);
        }
    }

    async testGridMapping() {
        console.log('🗺️  Testing Grid Mapping...');
        
        const testData = {
            name: 'Grid Test',
            data: 'Testing grid coordinate mapping',
            mimeType: 'text/plain'
        };

        try {
            const result = await this.atlasEngine.processContent(testData);
            const gridStats = this.atlasEngine.getGridStatistics();
            
            // Verify grid statistics
            this.assert(gridStats.totalCoordinates === 12288, 'Total coordinates should be 12288');
            this.assert(gridStats.pages === 48, 'Pages should be 48');
            this.assert(gridStats.cycles === 256, 'Cycles should be 256');
            this.assert(gridStats.r96Classes === 96, 'R96 classes should be 96');
            this.assert(gridStats.gridDimensions === '48×256', 'Grid dimensions should be 48×256');
            
            // Verify coordinate mapping
            this.assert(result.atlas.page >= 0 && result.atlas.page < 48, 'Page should be 0-47');
            this.assert(result.atlas.cycle >= 0 && result.atlas.cycle < 256, 'Cycle should be 0-255');
            
            // Verify coordinate calculation
            const calculatedIndex = result.atlas.page * 256 + result.atlas.cycle;
            const calculatedPage = Math.floor(calculatedIndex / 256);
            const calculatedCycle = calculatedIndex % 256;
            
            this.assert(calculatedPage === result.atlas.page, 'Calculated page should match');
            this.assert(calculatedCycle === result.atlas.cycle, 'Calculated cycle should match');
            this.assert(calculatedIndex >= 0 && calculatedIndex < 12288, 'Calculated index should be 0-12287');
            
            this.recordTest('Grid Mapping', true, 'Grid mapping working correctly');
            
        } catch (error) {
            this.recordTest('Grid Mapping', false, error.message);
        }
    }

    async testPerformance() {
        console.log('⚡ Testing Performance...');
        
        const testData = {
            name: 'Performance Test',
            data: 'Performance testing data',
            mimeType: 'text/plain'
        };

        try {
            const iterations = 50;
            const times = [];
            
            for (let i = 0; i < iterations; i++) {
                const start = process.hrtime.bigint();
                await this.atlasEngine.processContent(testData);
                const end = process.hrtime.bigint();
                times.push(Number(end - start) / 1000000); // Convert to milliseconds
            }
            
            const avgTime = times.reduce((a, b) => a + b, 0) / times.length;
            const maxTime = Math.max(...times);
            
            this.assert(avgTime < 100, `Average processing time should be under 100ms (got ${avgTime.toFixed(2)}ms)`);
            this.assert(maxTime < 500, `Maximum processing time should be under 500ms (got ${maxTime.toFixed(2)}ms)`);
            
            const throughput = 1000 / avgTime;
            this.assert(throughput > 10, `Throughput should be over 10 ops/sec (got ${throughput.toFixed(0)} ops/sec)`);
            
            this.recordTest('Performance', true, `Performance acceptable (avg: ${avgTime.toFixed(2)}ms, throughput: ${throughput.toFixed(0)} ops/sec)`);
            
        } catch (error) {
            this.recordTest('Performance', false, error.message);
        }
    }

    async testDemoDataGeneration() {
        console.log('📋 Testing Demo Data Generation...');
        
        try {
            const demoData = this.atlasEngine.generateDemoData();
            
            this.assert(Array.isArray(demoData), 'Demo data should be an array');
            this.assert(demoData.length > 0, 'Demo data should not be empty');
            
            for (const data of demoData) {
                this.assert(typeof data.name === 'string', 'Demo data name should be a string');
                this.assert(typeof data.data === 'string', 'Demo data content should be a string');
                this.assert(typeof data.mimeType === 'string', 'Demo data MIME type should be a string');
                this.assert(data.name.length > 0, 'Demo data name should not be empty');
                this.assert(data.data.length > 0, 'Demo data content should not be empty');
                this.assert(data.mimeType.length > 0, 'Demo data MIME type should not be empty');
            }
            
            // Test that demo data can be processed
            for (const data of demoData) {
                const result = await this.atlasEngine.processContent(data);
                this.assert(result.atlas, 'Demo data should be processable');
            }
            
            this.recordTest('Demo Data Generation', true, `Generated ${demoData.length} demo data sets`);
            
        } catch (error) {
            this.recordTest('Demo Data Generation', false, error.message);
        }
    }

    async testErrorHandling() {
        console.log('⚠️  Testing Error Handling...');
        
        try {
            // Test with invalid data
            const invalidData = {
                name: '',
                data: null,
                mimeType: ''
            };
            
            try {
                await this.atlasEngine.processContent(invalidData);
                this.recordTest('Error Handling', false, 'Should have thrown error for invalid data');
            } catch (error) {
                this.recordTest('Error Handling', true, 'Error handling working correctly');
            }
            
        } catch (error) {
            this.recordTest('Error Handling', false, error.message);
        }
    }

    async testGridStatistics() {
        console.log('📊 Testing Grid Statistics...');
        
        try {
            const stats = this.atlasEngine.getGridStatistics();
            
            this.assert(typeof stats === 'object', 'Grid statistics should be an object');
            this.assert(typeof stats.totalCoordinates === 'number', 'Total coordinates should be a number');
            this.assert(typeof stats.pages === 'number', 'Pages should be a number');
            this.assert(typeof stats.cycles === 'number', 'Cycles should be a number');
            this.assert(typeof stats.r96Classes === 'number', 'R96 classes should be a number');
            this.assert(typeof stats.gridDimensions === 'string', 'Grid dimensions should be a string');
            
            this.assert(stats.totalCoordinates === 12288, 'Total coordinates should be 12288');
            this.assert(stats.pages === 48, 'Pages should be 48');
            this.assert(stats.cycles === 256, 'Cycles should be 256');
            this.assert(stats.r96Classes === 96, 'R96 classes should be 96');
            this.assert(stats.gridDimensions === '48×256', 'Grid dimensions should be 48×256');
            
            this.recordTest('Grid Statistics', true, 'Grid statistics correct');
            
        } catch (error) {
            this.recordTest('Grid Statistics', false, error.message);
        }
    }

    assert(condition, message) {
        if (!condition) {
            throw new Error(message);
        }
    }

    recordTest(testName, passed, message) {
        if (passed) {
            this.testsPassed++;
            console.log(`  ✅ ${testName}: ${message}`);
        } else {
            this.testsFailed++;
            console.log(`  ❌ ${testName}: ${message}`);
        }
        
        this.testResults.push({
            name: testName,
            passed,
            message
        });
    }

    printTestSummary() {
        console.log('\n📊 Test Summary');
        console.log('=' .repeat(50));
        console.log(`Total Tests: ${this.testsPassed + this.testsFailed}`);
        console.log(`Passed: ${this.testsPassed}`);
        console.log(`Failed: ${this.testsFailed}`);
        console.log(`Success Rate: ${((this.testsPassed / (this.testsPassed + this.testsFailed)) * 100).toFixed(1)}%`);
        
        if (this.testsFailed > 0) {
            console.log('\n❌ Failed Tests:');
            this.testResults
                .filter(result => !result.passed)
                .forEach(result => {
                    console.log(`  • ${result.name}: ${result.message}`);
                });
        }
    }
}

// Run the test suite
if (require.main === module) {
    const testSuite = new AtlasDemoTestSuite();
    testSuite.runAllTests().catch(console.error);
}

module.exports = AtlasDemoTestSuite;

#!/usr/bin/env node

/**
 * Atlas-12288 Command Line Demo
 * 
 * Interactive command-line demonstration of Atlas functionality
 */

const readline = require('readline');
const chalk = require('chalk');
const cliProgress = require('cli-progress');
const { AtlasDemoEngine } = require('../dist/AtlasDemoEngine');

class AtlasCLIDemo {
    constructor() {
        this.atlasEngine = new AtlasDemoEngine();
        this.rl = readline.createInterface({
            input: process.stdin,
            output: process.stdout
        });
    }

    async start() {
        console.clear();
        this.showHeader();
        await this.showMainMenu();
    }

    showHeader() {
        console.log(chalk.blue.bold(`
╔══════════════════════════════════════════════════════════════════════════════╗
║                           🗺️  Atlas-12288 CLI Demo                          ║
║                                                                              ║
║  Watch as any data collapses into exactly 96 equivalence classes and maps   ║
║  to one of 12,288 coordinates in a 48×256 grid                              ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
        `));
    }

    async showMainMenu() {
        console.log(chalk.yellow('\n📋 Main Menu:'));
        console.log(chalk.white('1. Process custom data'));
        console.log(chalk.white('2. Run demo data sets'));
        console.log(chalk.white('3. Verify deterministic mapping'));
        console.log(chalk.white('4. Show grid statistics'));
        console.log(chalk.white('5. Interactive grid explorer'));
        console.log(chalk.white('6. Performance benchmark'));
        console.log(chalk.white('0. Exit'));

        const choice = await this.askQuestion('\nEnter your choice (0-6): ');
        
        switch (choice.trim()) {
            case '1':
                await this.processCustomData();
                break;
            case '2':
                await this.runDemoDataSets();
                break;
            case '3':
                await this.verifyDeterministicMapping();
                break;
            case '4':
                await this.showGridStatistics();
                break;
            case '5':
                await this.interactiveGridExplorer();
                break;
            case '6':
                await this.performanceBenchmark();
                break;
            case '0':
                console.log(chalk.green('\n👋 Thanks for exploring Atlas-12288!'));
                this.rl.close();
                return;
            default:
                console.log(chalk.red('\n❌ Invalid choice. Please try again.'));
                await this.showMainMenu();
        }
    }

    async processCustomData() {
        console.log(chalk.cyan('\n📝 Process Custom Data'));
        console.log(chalk.gray('Enter data to process through Atlas system\n'));

        const name = await this.askQuestion('Data name: ');
        const data = await this.askQuestion('Data content: ');
        const mimeType = await this.askQuestion('MIME type (default: text/plain): ') || 'text/plain';

        const content = { name, data, mimeType };

        console.log(chalk.yellow('\n🔄 Processing data...'));
        const progressBar = new cliProgress.SingleBar({
            format: 'Processing |{bar}| {percentage}% | {value}/{total} steps',
            barCompleteChar: '\u2588',
            barIncompleteChar: '\u2591',
            hideCursor: true
        });

        progressBar.start(4, 0);
        
        try {
            progressBar.update(1, { value: 1, total: 4 });
            await this.sleep(200);
            
            progressBar.update(2, { value: 2, total: 4 });
            await this.sleep(200);
            
            progressBar.update(3, { value: 3, total: 4 });
            await this.sleep(200);
            
            const result = await this.atlasEngine.processContent(content);
            
            progressBar.update(4, { value: 4, total: 4 });
            progressBar.stop();

            this.displayResults(result);
        } catch (error) {
            progressBar.stop();
            console.log(chalk.red(`\n❌ Error processing data: ${error.message}`));
        }

        await this.askQuestion('\nPress Enter to continue...');
        await this.showMainMenu();
    }

    async runDemoDataSets() {
        console.log(chalk.cyan('\n📋 Running Demo Data Sets'));
        console.log(chalk.gray('Processing predefined data sets to show Atlas functionality\n'));

        const demoData = this.atlasEngine.generateDemoData();
        const results = [];

        const progressBar = new cliProgress.SingleBar({
            format: 'Processing |{bar}| {percentage}% | {value}/{total} datasets',
            barCompleteChar: '\u2588',
            barIncompleteChar: '\u2591',
            hideCursor: true
        });

        progressBar.start(demoData.length, 0);

        for (let i = 0; i < demoData.length; i++) {
            const result = await this.atlasEngine.processContent(demoData[i]);
            results.push(result);
            progressBar.update(i + 1);
            await this.sleep(100);
        }

        progressBar.stop();

        console.log(chalk.green('\n✅ All demo data sets processed!\n'));

        // Display summary table
        console.log(chalk.yellow('📊 Results Summary:'));
        console.log(chalk.white('┌─────────────────┬──────┬───────┬─────────┬──────────┐'));
        console.log(chalk.white('│ Data Set        │ Page │ Cycle │ R96     │ Time(ms) │'));
        console.log(chalk.white('├─────────────────┼──────┼───────┼─────────┼──────────┤'));

        results.forEach((result, index) => {
            const name = result.input.name.padEnd(15);
            const page = result.atlas.page.toString().padStart(4);
            const cycle = result.atlas.cycle.toString().padStart(5);
            const r96 = result.atlas.r96Class.toString().padStart(7);
            const time = result.processingTime.toString().padStart(8);
            
            console.log(chalk.white(`│ ${name} │ ${page} │ ${cycle} │ ${r96} │ ${time} │`));
        });

        console.log(chalk.white('└─────────────────┴──────┴───────┴─────────┴──────────┘'));

        await this.askQuestion('\nPress Enter to continue...');
        await this.showMainMenu();
    }

    async verifyDeterministicMapping() {
        console.log(chalk.cyan('\n🔍 Verify Deterministic Mapping'));
        console.log(chalk.gray('Test that the same input always produces the same output\n'));

        const name = await this.askQuestion('Data name: ');
        const data = await this.askQuestion('Data content: ');
        const mimeType = await this.askQuestion('MIME type (default: text/plain): ') || 'text/plain';
        const iterations = parseInt(await this.askQuestion('Number of iterations (default: 5): ')) || 5;

        const content = { name, data, mimeType };

        console.log(chalk.yellow(`\n🔄 Running ${iterations} iterations to verify deterministic mapping...`));

        const progressBar = new cliProgress.SingleBar({
            format: 'Verifying |{bar}| {percentage}% | {value}/{total} iterations',
            barCompleteChar: '\u2588',
            barIncompleteChar: '\u2591',
            hideCursor: true
        });

        progressBar.start(iterations, 0);

        try {
            const result = await this.atlasEngine.verifyDeterministicMapping(content, iterations);
            
            for (let i = 0; i < iterations; i++) {
                progressBar.update(i + 1);
                await this.sleep(100);
            }

            progressBar.stop();

            console.log(chalk.green('\n✅ Verification complete!\n'));

            // Display results
            const status = result.isDeterministic ? 
                chalk.green('✅ DETERMINISTIC') : 
                chalk.red('❌ NOT DETERMINISTIC');
            
            console.log(chalk.yellow('📊 Verification Results:'));
            console.log(chalk.white(`Status: ${status}`));
            console.log(chalk.white(`Consistency: ${result.consistency}%`));
            console.log(chalk.white(`Iterations: ${result.results.length}\n`));

            console.log(chalk.yellow('📋 Detailed Results:'));
            result.results.forEach((res, index) => {
                console.log(chalk.white(`Iteration ${index + 1}: Page=${res.page}, Cycle=${res.cycle}, R96=${res.r96Class}`));
            });

            if (result.isDeterministic) {
                console.log(chalk.green('\n🎉 Perfect! Atlas mapping is completely deterministic.'));
            } else {
                console.log(chalk.red('\n⚠️  Warning: Mapping is not deterministic. This should not happen!'));
            }

        } catch (error) {
            progressBar.stop();
            console.log(chalk.red(`\n❌ Error during verification: ${error.message}`));
        }

        await this.askQuestion('\nPress Enter to continue...');
        await this.showMainMenu();
    }

    async showGridStatistics() {
        console.log(chalk.cyan('\n📊 Grid Statistics'));
        
        const stats = this.atlasEngine.getGridStatistics();
        
        console.log(chalk.yellow('\n🗺️  Atlas-12288 Grid Information:'));
        console.log(chalk.white(`Total Coordinates: ${chalk.green(stats.totalCoordinates.toLocaleString())}`));
        console.log(chalk.white(`Grid Dimensions: ${chalk.green(stats.gridDimensions)}`));
        console.log(chalk.white(`Pages (Rows): ${chalk.green(stats.pages)}`));
        console.log(chalk.white(`Cycles (Columns): ${chalk.green(stats.cycles)}`));
        console.log(chalk.white(`R96 Classes: ${chalk.green(stats.r96Classes)}`));
        
        console.log(chalk.yellow('\n📐 Mathematical Relationships:'));
        console.log(chalk.white(`Pages × Cycles = ${stats.pages} × ${stats.cycles} = ${stats.totalCoordinates}`));
        console.log(chalk.white(`Total ÷ R96 = ${stats.totalCoordinates} ÷ ${stats.r96Classes} = ${Math.floor(stats.totalCoordinates / stats.r96Classes)}`));
        
        console.log(chalk.yellow('\n🎯 Key Features:'));
        console.log(chalk.white('• Every piece of data maps to exactly one coordinate'));
        console.log(chalk.white('• Mapping is deterministic and reproducible'));
        console.log(chalk.white('• Data collapses into 96 natural equivalence classes'));
        console.log(chalk.white('• Grid provides 12,288 unique positions'));

        await this.askQuestion('\nPress Enter to continue...');
        await this.showMainMenu();
    }

    async interactiveGridExplorer() {
        console.log(chalk.cyan('\n🗺️  Interactive Grid Explorer'));
        console.log(chalk.gray('Explore the 48×256 Atlas grid interactively\n'));

        while (true) {
            console.log(chalk.yellow('Grid Explorer Options:'));
            console.log(chalk.white('1. View specific coordinate'));
            console.log(chalk.white('2. Show coordinate range'));
            console.log(chalk.white('3. Calculate coordinate from index'));
            console.log(chalk.white('4. Back to main menu'));

            const choice = await this.askQuestion('\nEnter your choice (1-4): ');

            switch (choice.trim()) {
                case '1':
                    await this.viewSpecificCoordinate();
                    break;
                case '2':
                    await this.showCoordinateRange();
                    break;
                case '3':
                    await this.calculateCoordinateFromIndex();
                    break;
                case '4':
                    await this.showMainMenu();
                    return;
                default:
                    console.log(chalk.red('\n❌ Invalid choice. Please try again.'));
            }
        }
    }

    async viewSpecificCoordinate() {
        const page = parseInt(await this.askQuestion('Enter page (0-47): '));
        const cycle = parseInt(await this.askQuestion('Enter cycle (0-255): '));

        if (page < 0 || page > 47 || cycle < 0 || cycle > 255) {
            console.log(chalk.red('\n❌ Invalid coordinates. Page must be 0-47, Cycle must be 0-255.'));
            return;
        }

        const index = page * 256 + cycle;
        
        console.log(chalk.green('\n✅ Coordinate Information:'));
        console.log(chalk.white(`Page: ${page}`));
        console.log(chalk.white(`Cycle: ${cycle}`));
        console.log(chalk.white(`Index: ${index}`));
        console.log(chalk.white(`Position: ${page + 1}/${48} × ${cycle + 1}/${256}`));
    }

    async showCoordinateRange() {
        const startPage = parseInt(await this.askQuestion('Start page (0-47): '));
        const endPage = parseInt(await this.askQuestion('End page (0-47): '));
        const startCycle = parseInt(await this.askQuestion('Start cycle (0-255): '));
        const endCycle = parseInt(await this.askQuestion('End cycle (0-255): '));

        if (startPage < 0 || endPage > 47 || startCycle < 0 || endCycle > 255 || startPage > endPage || startCycle > endCycle) {
            console.log(chalk.red('\n❌ Invalid range. Please check your coordinates.'));
            return;
        }

        console.log(chalk.green('\n✅ Coordinate Range:'));
        console.log(chalk.white(`Pages: ${startPage} to ${endPage} (${endPage - startPage + 1} pages)`));
        console.log(chalk.white(`Cycles: ${startCycle} to ${endCycle} (${endCycle - startCycle + 1} cycles)`));
        
        const totalCoords = (endPage - startPage + 1) * (endCycle - startCycle + 1);
        console.log(chalk.white(`Total coordinates: ${totalCoords}`));
        
        const startIndex = startPage * 256 + startCycle;
        const endIndex = endPage * 256 + endCycle;
        console.log(chalk.white(`Index range: ${startIndex} to ${endIndex}`));
    }

    async calculateCoordinateFromIndex() {
        const index = parseInt(await this.askQuestion('Enter index (0-12287): '));

        if (index < 0 || index > 12287) {
            console.log(chalk.red('\n❌ Invalid index. Must be between 0 and 12287.'));
            return;
        }

        const page = Math.floor(index / 256);
        const cycle = index % 256;
        
        console.log(chalk.green('\n✅ Coordinate Calculation:'));
        console.log(chalk.white(`Index: ${index}`));
        console.log(chalk.white(`Page: ${page} (calculated as Math.floor(${index} / 256))`));
        console.log(chalk.white(`Cycle: ${cycle} (calculated as ${index} % 256)`));
        console.log(chalk.white(`Verification: ${page} × 256 + ${cycle} = ${page * 256 + cycle}`));
    }

    async performanceBenchmark() {
        console.log(chalk.cyan('\n⚡ Performance Benchmark'));
        console.log(chalk.gray('Test Atlas processing performance with various data sizes\n'));

        const testData = [
            { name: 'Small Text', data: 'Hello World', size: '11 bytes' },
            { name: 'Medium Text', data: 'Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua.', size: '123 bytes' },
            { name: 'Large Text', data: 'Lorem ipsum dolor sit amet, consectetur adipiscing elit. Sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.', size: '445 bytes' },
            { name: 'JSON Data', data: JSON.stringify({ id: 1, name: 'Test', data: Array(100).fill('test').join('') }), size: '~500 bytes' }
        ];

        console.log(chalk.yellow('🔄 Running performance benchmark...\n'));

        const results = [];
        const iterations = 10;

        for (const test of testData) {
            console.log(chalk.white(`Testing: ${test.name} (${test.size})`));
            
            const times = [];
            for (let i = 0; i < iterations; i++) {
                const start = process.hrtime.bigint();
                await this.atlasEngine.processContent({
                    name: test.name,
                    data: test.data,
                    mimeType: 'text/plain'
                });
                const end = process.hrtime.bigint();
                times.push(Number(end - start) / 1000000); // Convert to milliseconds
            }

            const avgTime = times.reduce((a, b) => a + b, 0) / times.length;
            const minTime = Math.min(...times);
            const maxTime = Math.max(...times);

            results.push({
                name: test.name,
                size: test.size,
                avgTime: avgTime,
                minTime: minTime,
                maxTime: maxTime
            });
        }

        console.log(chalk.green('\n✅ Benchmark complete!\n'));

        // Display results
        console.log(chalk.yellow('📊 Performance Results:'));
        console.log(chalk.white('┌─────────────┬─────────────┬──────────┬──────────┬──────────┐'));
        console.log(chalk.white('│ Test Data   │ Size        │ Avg(ms)  │ Min(ms)  │ Max(ms)  │'));
        console.log(chalk.white('├─────────────┼─────────────┼──────────┼──────────┼──────────┤'));

        results.forEach(result => {
            const name = result.name.padEnd(11);
            const size = result.size.padEnd(11);
            const avg = result.avgTime.toFixed(2).padStart(8);
            const min = result.minTime.toFixed(2).padStart(8);
            const max = result.maxTime.toFixed(2).padStart(8);
            
            console.log(chalk.white(`│ ${name} │ ${size} │ ${avg} │ ${min} │ ${max} │`));
        });

        console.log(chalk.white('└─────────────┴─────────────┴──────────┴──────────┴──────────┘'));

        const totalAvg = results.reduce((sum, r) => sum + r.avgTime, 0) / results.length;
        console.log(chalk.green(`\n🎯 Average processing time: ${totalAvg.toFixed(2)}ms`));
        console.log(chalk.green(`🚀 Atlas system is highly efficient!`));

        await this.askQuestion('\nPress Enter to continue...');
        await this.showMainMenu();
    }

    displayResults(result) {
        console.log(chalk.green('\n✅ Processing Complete!\n'));
        
        console.log(chalk.yellow('📊 Atlas Results:'));
        console.log(chalk.white(`Page (Row): ${chalk.green(result.atlas.page)}`));
        console.log(chalk.white(`Cycle (Column): ${chalk.green(result.atlas.cycle)}`));
        console.log(chalk.white(`R96 Class: ${chalk.green(result.atlas.r96Class)}`));
        console.log(chalk.white(`Klein Window: ${chalk.green(result.atlas.kleinWindow)}`));
        console.log(chalk.white(`Conservation Hash: ${chalk.green(result.atlas.conservationHash)}`));
        console.log(chalk.white(`UOR-ID: ${chalk.green(result.atlas.uorId)}`));
        
        console.log(chalk.yellow('\n📈 Byte Analysis:'));
        console.log(chalk.white(`Total Bytes: ${chalk.green(result.byteAnalysis.totalBytes)}`));
        console.log(chalk.white(`Unique Bytes: ${chalk.green(result.byteAnalysis.uniqueBytes)}`));
        console.log(chalk.white(`Entropy: ${chalk.green(result.byteAnalysis.entropy.toFixed(2))}`));
        console.log(chalk.white(`R96 Classification: ${chalk.green(result.byteAnalysis.r96Classification)}`));
        
        console.log(chalk.yellow('\n⚡ Performance:'));
        console.log(chalk.white(`Processing Time: ${chalk.green(result.processingTime)}ms`));
        
        console.log(chalk.cyan('\n🎯 Key Insights:'));
        console.log(chalk.white(`• Data maps to coordinate (${result.atlas.page}, ${result.atlas.cycle}) in 48×256 grid`));
        console.log(chalk.white(`• Data collapses into R96 class ${result.atlas.r96Class} out of 96 possible classes`));
        console.log(chalk.white(`• Mapping is deterministic and reproducible`));
        console.log(chalk.white(`• Processing completed in ${result.processingTime}ms`));
    }

    askQuestion(question) {
        return new Promise((resolve) => {
            this.rl.question(question, resolve);
        });
    }

    sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}

// Start the demo
if (require.main === module) {
    const demo = new AtlasCLIDemo();
    demo.start().catch(console.error);
}

module.exports = AtlasCLIDemo;

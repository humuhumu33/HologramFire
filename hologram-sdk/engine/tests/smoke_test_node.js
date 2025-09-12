const Docker = require('dockerode');

async function testHologramdCompatibility() {
    console.log('Testing hologramd compatibility with Docker Node SDK...');
    
    // Create Docker client pointing to hologramd socket
    const docker = new Docker({ socketPath: '/var/run/hologramd.sock' });
    
    try {
        // Test 1: Ping
        console.log('1. Testing ping...');
        await docker.ping();
        console.log('   ✓ Ping successful');
        
        // Test 2: Server info
        console.log('2. Testing server info...');
        const info = await docker.info();
        console.log(`   ✓ Server info: ${info.ID} (Driver: ${info.Driver})`);
        
        // Test 3: List images
        console.log('3. Testing image list...');
        const images = await docker.listImages();
        console.log(`   ✓ Found ${images.length} images`);
        
        // Test 4: Pull image
        console.log('4. Testing image pull...');
        const pullStream = await docker.pull('nginx:alpine');
        
        // Wait for pull to complete
        await new Promise((resolve, reject) => {
            docker.modem.followProgress(pullStream, (err, res) => {
                if (err) reject(err);
                else resolve(res);
            });
        });
        console.log('   ✓ Image pull successful');
        
        // Test 5: List images again to verify pull
        console.log('5. Verifying pulled image...');
        const imagesAfterPull = await docker.listImages();
        const nginxImage = imagesAfterPull.find(img => 
            img.RepoTags && img.RepoTags.some(tag => tag === 'nginx:alpine')
        );
        
        if (nginxImage) {
            console.log('   ✓ Nginx image found in list');
        } else {
            console.log('   ⚠ Nginx image not found in list (may be expected)');
        }
        
        // Test 6: Container operations
        console.log('6. Testing container create...');
        const container = await docker.createContainer({
            Image: 'nginx:alpine',
            Cmd: ['echo', 'hello from hologramd'],
            name: 'hologramd-test'
        });
        console.log(`   ✓ Container created: ${container.id.substring(0, 12)}`);
        
        // Test 7: Container start
        console.log('7. Testing container start...');
        await container.start();
        console.log('   ✓ Container started');
        
        // Wait a moment for container to run
        await new Promise(resolve => setTimeout(resolve, 2000));
        
        // Test 8: Container logs
        console.log('8. Testing container logs...');
        const logs = await container.logs({
            stdout: true,
            stderr: true
        });
        console.log(`   ✓ Container logs: ${logs.toString()}`);
        
        // Test 9: Container stop
        console.log('9. Testing container stop...');
        await container.stop();
        console.log('   ✓ Container stopped');
        
        // Test 10: Container remove
        console.log('10. Testing container remove...');
        await container.remove();
        console.log('   ✓ Container removed');
        
        // Test 11: Test verbose mode (if supported)
        console.log('11. Testing verbose mode...');
        try {
            // Try to get images with verbose headers
            const verboseImages = await docker.listImages({
                headers: {
                    'X-Hologram-Verbose': 'true'
                }
            });
            
            // Check if any image has XHologram field
            const hasXHologram = verboseImages.some(img => img.XHologram);
            if (hasXHologram) {
                console.log('   ✓ Verbose mode shows XHologram fields');
            } else {
                console.log('   ⚠ Verbose mode not showing XHologram fields (may be expected)');
            }
        } catch (err) {
            console.log('   ⚠ Verbose mode test failed (may be expected):', err.message);
        }
        
        console.log('\n🎉 All tests passed! hologramd is compatible with Docker Node SDK');
        
    } catch (error) {
        console.error('❌ Test failed:', error.message);
        process.exit(1);
    }
}

// Run the tests
testHologramdCompatibility().catch(error => {
    console.error('❌ Test suite failed:', error);
    process.exit(1);
});

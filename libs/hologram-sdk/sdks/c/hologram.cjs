// Delegates stdin JSON to the reference CLI and prints the response.
// Enhanced with timeout protection and better error handling.
const { spawn } = require("node:child_process");

const REF = process.env.HOLOGRAM_SDK_REF
  || `npx ts-node --transpile-only sdk/ref/cli.ts`;

(async () => {
  // Parse the REF command to handle both simple commands and shell commands
  const refParts = REF.split(' ');
  const command = refParts[0];
  const args = refParts.slice(1);
  
  const p = spawn(command, args, { 
    stdio: ["pipe", "pipe", "inherit"], 
    shell: false,
    timeout: 10000 // 10 second timeout
  });

  // Handle process errors
  p.on('error', (err) => {
    console.error('[hologram:c] spawn error:', err.message);
    process.exit(1);
  });

  // Handle timeout
  const timeout = setTimeout(() => {
    p.kill('SIGTERM');
    console.error('[hologram:c] process timed out after 10 seconds');
    process.exit(1);
  }, 10000);

  p.on("exit", (code, signal) => {
    clearTimeout(timeout);
    if (signal) {
      console.error(`[hologram:c] process killed by signal: ${signal}`);
      process.exit(1);
    }
    process.exit(code ?? 0);
  });

  // Pipe streams
  process.stdin.pipe(p.stdin);
  
  let output = '';
  p.stdout.on('data', (data) => {
    output += data.toString();
  });
  
  p.stdout.on('end', () => {
    process.stdout.write(output);
  });
})();

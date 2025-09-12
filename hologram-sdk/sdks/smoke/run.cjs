// sdk/smoke/run.cjs
// Sends {"method":"version"} to a given CLI and prints the JSON reply.
// Cross-platform: uses Node to spawn the target with a shell when needed.
// Enhanced with timeout protection, better error handling, and performance monitoring.

const cp = require("node:child_process");

const cmd = process.argv.slice(2).join(" ").trim();
if (!cmd) {
  console.error("usage: node sdk/smoke/run.cjs \"<command>\"");
  process.exit(2);
}

// Delegate reference (works after `npm ci`)
const REF = "npx ts-node --transpile-only sdk/ref/cli.ts";

const env = { ...process.env, HOLOGRAM_SDK_REF: REF };
const req = JSON.stringify({ method: "version" });

// Enhanced options with timeout and better error handling
const options = {
  input: req,
  encoding: "utf8",
  env,
  shell: true,
  timeout: 10000, // 10 second timeout
  maxBuffer: 1024 * 1024, // 1MB buffer
  killSignal: 'SIGTERM'
};

const startTime = Date.now();
const p = cp.spawnSync(cmd, options);
const duration = Date.now() - startTime;

if (p.error) {
  console.error(`[sdk:smoke] spawn error (${duration}ms):`, p.error.message);
  if (p.error.code === 'ETIMEDOUT') {
    console.error("[sdk:smoke] command timed out after 10 seconds");
  }
  process.exit(1);
}

if (p.signal) {
  console.error(`[sdk:smoke] process killed by signal: ${p.signal} (${duration}ms)`);
  process.exit(1);
}

const out = (p.stdout || "").trim();
if (!out) {
  console.error(`[sdk:smoke] empty stdout from command: ${cmd} (${duration}ms)`);
  if (p.stderr) {
    console.error("[sdk:smoke] stderr:", p.stderr.trim());
  }
  process.exit(p.status ?? 1);
}

// Validate JSON response
try {
  JSON.parse(out);
} catch (e) {
  console.error(`[sdk:smoke] invalid JSON response (${duration}ms):`, out);
  process.exit(1);
}

console.log(out);
process.exit(p.status ?? 0);

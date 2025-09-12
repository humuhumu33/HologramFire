#!/usr/bin/env ts-node

import fs from "node:fs";
import path from "node:path";

/**
 * Generate a release-friendly performance report from attestation and longrun artifacts
 */

interface PerfResult {
  name: string;
  iters: number;
  nsPerOp: number;
  opsPerSec: number;
  p50: number;
  p95: number;
  p99: number;
  cpuPerOpNs?: number;
  jPerOp?: number;
  wattsEff?: number;
  witness: string;
}

interface Attestation {
  v: number;
  ts: string;
  host: { node: string; platform: string; arch: string };
  repo: { commit: string };
  blueprint: { digest: string };
  config: { runs: number; warmup: number; iters: number; itersTransport: number };
  results: PerfResult[];
  suiteWitness: string;
}

interface LongrunResult {
  name: string;
  nsPerOp: number;
  p95: number;
  cpuPerOpNs?: number;
  jPerOp?: number;
  witness: string;
}

interface Longrun {
  v: number;
  windows: number;
  perWindowRuns: number;
  warmupOps: number;
  iters: number;
  itersTransport: number;
  maxDrift: number;
  stability: { violations: string[] };
  results: LongrunResult[];
  suiteWitness: string;
}

function formatNumber(num: number, decimals = 0): string {
  return num.toLocaleString(undefined, { 
    minimumFractionDigits: decimals, 
    maximumFractionDigits: decimals 
  });
}

function formatOpsPerSec(ops: number): string {
  if (ops >= 1000000) return `${(ops / 1000000).toFixed(1)}M ops/s`;
  if (ops >= 1000) return `${(ops / 1000).toFixed(1)}K ops/s`;
  return `${formatNumber(ops)} ops/s`;
}

function formatLatency(ns: number): string {
  if (ns >= 1000000) return `${(ns / 1000000).toFixed(1)}ms`;
  if (ns >= 1000) return `${(ns / 1000).toFixed(1)}μs`;
  return `${formatNumber(ns)}ns`;
}

function formatEnergy(joules: number): string {
  if (joules >= 0.001) return `${(joules * 1000).toFixed(2)}mJ`;
  return `${(joules * 1000000).toFixed(1)}μJ`;
}

function generateReport(attestationPath: string, longrunPath?: string): string {
  const att: Attestation = JSON.parse(fs.readFileSync(attestationPath, "utf8"));
  
  let longrun: Longrun | null = null;
  if (longrunPath && fs.existsSync(longrunPath)) {
    longrun = JSON.parse(fs.readFileSync(longrunPath, "utf8"));
  }

  const report = [
    "# Atlas-12288 Performance Report",
    "",
    `**Generated:** ${new Date(att.ts).toLocaleString()}`,
    `**Platform:** ${att.host.platform} ${att.host.arch} (Node ${att.host.node})`,
    `**Commit:** \`${att.repo.commit.substring(0, 8)}\``,
    `**Blueprint:** \`${att.blueprint.digest.substring(0, 8)}\``,
    "",
    "## Configuration",
    `- **Runs:** ${att.config.runs}`,
    `- **Warmup:** ${att.config.warmup}`,
    `- **Iterations:** ${att.config.iters}`,
    `- **Transport Iterations:** ${att.config.itersTransport}`,
    "",
    "## Performance Results",
    "",
    "| Benchmark | Throughput | Latency (p95) | CPU/Op | Energy/Op |",
    "|-----------|------------|---------------|--------|-----------|"
  ];

  for (const result of att.results) {
    const throughput = formatOpsPerSec(result.opsPerSec);
    const latency = formatLatency(result.p95);
    const cpu = result.cpuPerOpNs ? formatLatency(result.cpuPerOpNs) : "N/A";
    const energy = result.jPerOp ? formatEnergy(result.jPerOp) : "N/A";
    
    report.push(`| ${result.name} | ${throughput} | ${latency} | ${cpu} | ${energy} |`);
  }

  report.push("", "## Stability Analysis");
  
  if (longrun) {
    if (longrun.stability.violations.length === 0) {
      report.push("✅ **All benchmarks stable** - No drift violations detected");
    } else {
      report.push("⚠️ **Drift violations detected:**");
      for (const violation of longrun.stability.violations) {
        report.push(`- ${violation}`);
      }
    }
    
    report.push("", "### Long-run Configuration");
    report.push(`- **Windows:** ${longrun.windows}`);
    report.push(`- **Runs per Window:** ${longrun.perWindowRuns}`);
    report.push(`- **Max Drift:** ${(longrun.maxDrift * 100).toFixed(1)}%`);
  } else {
    report.push("ℹ️ Long-run stability data not available");
  }

  report.push("", "## Verification");
  report.push(`- **Suite Witness:** \`${att.suiteWitness.substring(0, 16)}...\``);
  if (longrun) {
    report.push(`- **Stability Witness:** \`${longrun.suiteWitness.substring(0, 16)}...\``);
  }

  return report.join("\n");
}

function main() {
  const args = process.argv.slice(2);
  
  if (args.includes("--help") || args.length === 0) {
    console.log(`
Performance Report Generator

Usage:
  ts-node perf-report.ts [options]

Options:
  --attestation <path>    Path to attestation.json (default: artifacts/perf/attestation.json)
  --longrun <path>        Path to longrun.json (default: artifacts/perf/longrun.json)
  --output <path>         Output file path (default: stdout)
  --help                  Show this help

Examples:
  ts-node perf-report.ts
  ts-node perf-report.ts --output perf-report.md
  ts-node perf-report.ts --attestation custom-attestation.json
`);
    process.exit(0);
  }

  const getFlag = (name: string, defaultValue: string): string => {
    const index = args.indexOf(`--${name}`);
    return index !== -1 && args[index + 1] ? args[index + 1] : defaultValue;
  };

  const attestationPath = getFlag("attestation", "artifacts/perf/attestation.json");
  const longrunPath = getFlag("longrun", "artifacts/perf/longrun.json");
  const outputPath = getFlag("output", "");

  if (!fs.existsSync(attestationPath)) {
    console.error(`❌ Attestation file not found: ${attestationPath}`);
    process.exit(1);
  }

  const report = generateReport(attestationPath, longrunPath);

  if (outputPath) {
    fs.writeFileSync(outputPath, report);
    console.log(`📊 Performance report written to: ${outputPath}`);
  } else {
    console.log(report);
  }
}

if (require.main === module) {
  main();
}
